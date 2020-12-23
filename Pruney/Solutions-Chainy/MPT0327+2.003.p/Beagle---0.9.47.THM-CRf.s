%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:31 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   44 (  54 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  45 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_30,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k1_tarski(A_23),B_24)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_164,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = A_42
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_327,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(k1_tarski(A_60),B_61) = k1_tarski(A_60)
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_24,c_164])).

tff(c_82,plain,(
    ! [B_32,A_33] : k3_xboole_0(B_32,A_33) = k3_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    ! [A_33,B_32] : k2_xboole_0(A_33,k3_xboole_0(B_32,A_33)) = A_33 ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_6])).

tff(c_372,plain,(
    ! [B_66,A_67] :
      ( k2_xboole_0(B_66,k1_tarski(A_67)) = B_66
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_97])).

tff(c_12,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_169,plain,(
    ! [A_44,B_45] : k3_tarski(k2_tarski(A_44,B_45)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_204,plain,(
    ! [B_47,A_48] : k3_tarski(k2_tarski(B_47,A_48)) = k2_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_169])).

tff(c_26,plain,(
    ! [A_25,B_26] : k3_tarski(k2_tarski(A_25,B_26)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_210,plain,(
    ! [B_47,A_48] : k2_xboole_0(B_47,A_48) = k2_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_26])).

tff(c_10,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_239,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_28])).

tff(c_240,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_10,c_239])).

tff(c_378,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_240])).

tff(c_408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_378])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.31  
% 1.90/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.31  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 1.90/1.31  
% 1.90/1.31  %Foreground sorts:
% 1.90/1.31  
% 1.90/1.31  
% 1.90/1.31  %Background operators:
% 1.90/1.31  
% 1.90/1.31  
% 1.90/1.31  %Foreground operators:
% 1.90/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.90/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.90/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.90/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.90/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.90/1.31  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.31  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.90/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.90/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.90/1.31  
% 2.17/1.32  tff(f_58, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 2.17/1.32  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.17/1.32  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.17/1.32  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.17/1.32  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.17/1.32  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.17/1.32  tff(f_53, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.17/1.32  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.17/1.32  tff(c_30, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.17/1.32  tff(c_24, plain, (![A_23, B_24]: (r1_tarski(k1_tarski(A_23), B_24) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.17/1.32  tff(c_164, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=A_42 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.32  tff(c_327, plain, (![A_60, B_61]: (k3_xboole_0(k1_tarski(A_60), B_61)=k1_tarski(A_60) | ~r2_hidden(A_60, B_61))), inference(resolution, [status(thm)], [c_24, c_164])).
% 2.17/1.32  tff(c_82, plain, (![B_32, A_33]: (k3_xboole_0(B_32, A_33)=k3_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.17/1.32  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.32  tff(c_97, plain, (![A_33, B_32]: (k2_xboole_0(A_33, k3_xboole_0(B_32, A_33))=A_33)), inference(superposition, [status(thm), theory('equality')], [c_82, c_6])).
% 2.17/1.32  tff(c_372, plain, (![B_66, A_67]: (k2_xboole_0(B_66, k1_tarski(A_67))=B_66 | ~r2_hidden(A_67, B_66))), inference(superposition, [status(thm), theory('equality')], [c_327, c_97])).
% 2.17/1.32  tff(c_12, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.17/1.32  tff(c_169, plain, (![A_44, B_45]: (k3_tarski(k2_tarski(A_44, B_45))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.32  tff(c_204, plain, (![B_47, A_48]: (k3_tarski(k2_tarski(B_47, A_48))=k2_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_12, c_169])).
% 2.17/1.32  tff(c_26, plain, (![A_25, B_26]: (k3_tarski(k2_tarski(A_25, B_26))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.32  tff(c_210, plain, (![B_47, A_48]: (k2_xboole_0(B_47, A_48)=k2_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_204, c_26])).
% 2.17/1.32  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.17/1.32  tff(c_28, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.17/1.32  tff(c_239, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_210, c_28])).
% 2.17/1.32  tff(c_240, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_210, c_10, c_239])).
% 2.17/1.32  tff(c_378, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_372, c_240])).
% 2.17/1.32  tff(c_408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_378])).
% 2.17/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.32  
% 2.17/1.32  Inference rules
% 2.17/1.32  ----------------------
% 2.17/1.32  #Ref     : 0
% 2.17/1.32  #Sup     : 91
% 2.17/1.32  #Fact    : 0
% 2.17/1.32  #Define  : 0
% 2.17/1.32  #Split   : 0
% 2.17/1.32  #Chain   : 0
% 2.17/1.32  #Close   : 0
% 2.17/1.32  
% 2.17/1.32  Ordering : KBO
% 2.17/1.32  
% 2.17/1.32  Simplification rules
% 2.17/1.32  ----------------------
% 2.17/1.32  #Subsume      : 2
% 2.17/1.32  #Demod        : 14
% 2.17/1.32  #Tautology    : 67
% 2.17/1.32  #SimpNegUnit  : 0
% 2.17/1.32  #BackRed      : 1
% 2.17/1.32  
% 2.17/1.32  #Partial instantiations: 0
% 2.17/1.32  #Strategies tried      : 1
% 2.17/1.33  
% 2.17/1.33  Timing (in seconds)
% 2.17/1.33  ----------------------
% 2.17/1.33  Preprocessing        : 0.31
% 2.17/1.33  Parsing              : 0.17
% 2.17/1.33  CNF conversion       : 0.02
% 2.17/1.33  Main loop            : 0.19
% 2.17/1.33  Inferencing          : 0.08
% 2.17/1.33  Reduction            : 0.06
% 2.17/1.33  Demodulation         : 0.05
% 2.17/1.33  BG Simplification    : 0.01
% 2.17/1.33  Subsumption          : 0.02
% 2.17/1.33  Abstraction          : 0.01
% 2.17/1.33  MUC search           : 0.00
% 2.17/1.33  Cooper               : 0.00
% 2.17/1.33  Total                : 0.52
% 2.17/1.33  Index Insertion      : 0.00
% 2.17/1.33  Index Deletion       : 0.00
% 2.17/1.33  Index Matching       : 0.00
% 2.17/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
