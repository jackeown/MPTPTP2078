%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:31 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   37 (  55 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  41 expanded)
%              Number of equality atoms :   15 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_61,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_38,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_204,plain,(
    ! [A_79,B_80] :
      ( k2_xboole_0(k1_tarski(A_79),B_80) = B_80
      | ~ r2_hidden(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_90,plain,(
    ! [A_68,B_69] : k3_tarski(k2_tarski(A_68,B_69)) = k2_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_134,plain,(
    ! [B_73,A_74] : k3_tarski(k2_tarski(B_73,A_74)) = k2_xboole_0(A_74,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_90])).

tff(c_34,plain,(
    ! [A_61,B_62] : k3_tarski(k2_tarski(A_61,B_62)) = k2_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_140,plain,(
    ! [B_73,A_74] : k2_xboole_0(B_73,A_74) = k2_xboole_0(A_74,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_34])).

tff(c_243,plain,(
    ! [B_81,A_82] :
      ( k2_xboole_0(B_81,k1_tarski(A_82)) = B_81
      | ~ r2_hidden(A_82,B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_140])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_193,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_4,c_140,c_36])).

tff(c_253,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_193])).

tff(c_287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_253])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:14:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.18  
% 2.00/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.18  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.00/1.18  
% 2.00/1.18  %Foreground sorts:
% 2.00/1.18  
% 2.00/1.18  
% 2.00/1.18  %Background operators:
% 2.00/1.18  
% 2.00/1.18  
% 2.00/1.18  %Foreground operators:
% 2.00/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.00/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.00/1.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.00/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.00/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.18  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.18  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.00/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.00/1.18  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.18  
% 2.00/1.19  tff(f_66, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 2.00/1.19  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 2.00/1.19  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.00/1.19  tff(f_61, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_zfmisc_1)).
% 2.00/1.19  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.00/1.19  tff(c_38, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.00/1.19  tff(c_204, plain, (![A_79, B_80]: (k2_xboole_0(k1_tarski(A_79), B_80)=B_80 | ~r2_hidden(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.00/1.19  tff(c_10, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.00/1.19  tff(c_90, plain, (![A_68, B_69]: (k3_tarski(k2_tarski(A_68, B_69))=k2_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.00/1.19  tff(c_134, plain, (![B_73, A_74]: (k3_tarski(k2_tarski(B_73, A_74))=k2_xboole_0(A_74, B_73))), inference(superposition, [status(thm), theory('equality')], [c_10, c_90])).
% 2.00/1.19  tff(c_34, plain, (![A_61, B_62]: (k3_tarski(k2_tarski(A_61, B_62))=k2_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.00/1.19  tff(c_140, plain, (![B_73, A_74]: (k2_xboole_0(B_73, A_74)=k2_xboole_0(A_74, B_73))), inference(superposition, [status(thm), theory('equality')], [c_134, c_34])).
% 2.00/1.19  tff(c_243, plain, (![B_81, A_82]: (k2_xboole_0(B_81, k1_tarski(A_82))=B_81 | ~r2_hidden(A_82, B_81))), inference(superposition, [status(thm), theory('equality')], [c_204, c_140])).
% 2.00/1.19  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.19  tff(c_36, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.00/1.19  tff(c_193, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_4, c_140, c_36])).
% 2.00/1.19  tff(c_253, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_243, c_193])).
% 2.00/1.19  tff(c_287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_253])).
% 2.00/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.19  
% 2.00/1.19  Inference rules
% 2.00/1.19  ----------------------
% 2.00/1.19  #Ref     : 0
% 2.00/1.19  #Sup     : 61
% 2.00/1.19  #Fact    : 0
% 2.00/1.19  #Define  : 0
% 2.00/1.19  #Split   : 0
% 2.00/1.19  #Chain   : 0
% 2.00/1.19  #Close   : 0
% 2.00/1.19  
% 2.00/1.19  Ordering : KBO
% 2.00/1.19  
% 2.00/1.19  Simplification rules
% 2.00/1.19  ----------------------
% 2.00/1.19  #Subsume      : 2
% 2.00/1.19  #Demod        : 7
% 2.00/1.19  #Tautology    : 38
% 2.00/1.19  #SimpNegUnit  : 0
% 2.00/1.19  #BackRed      : 0
% 2.00/1.19  
% 2.00/1.19  #Partial instantiations: 0
% 2.00/1.19  #Strategies tried      : 1
% 2.00/1.19  
% 2.00/1.19  Timing (in seconds)
% 2.00/1.19  ----------------------
% 2.00/1.19  Preprocessing        : 0.30
% 2.00/1.19  Parsing              : 0.16
% 2.00/1.19  CNF conversion       : 0.02
% 2.00/1.19  Main loop            : 0.15
% 2.00/1.19  Inferencing          : 0.05
% 2.00/1.19  Reduction            : 0.05
% 2.00/1.19  Demodulation         : 0.05
% 2.00/1.19  BG Simplification    : 0.02
% 2.00/1.19  Subsumption          : 0.02
% 2.00/1.19  Abstraction          : 0.01
% 2.00/1.20  MUC search           : 0.00
% 2.00/1.20  Cooper               : 0.00
% 2.00/1.20  Total                : 0.47
% 2.00/1.20  Index Insertion      : 0.00
% 2.00/1.20  Index Deletion       : 0.00
% 2.00/1.20  Index Matching       : 0.00
% 2.00/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
