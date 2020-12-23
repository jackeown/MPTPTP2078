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
% DateTime   : Thu Dec  3 09:50:58 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   40 (  43 expanded)
%              Number of leaves         :   26 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  36 expanded)
%              Number of equality atoms :   14 (  17 expanded)
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

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_38,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_337,plain,(
    ! [A_81,B_82,C_83] :
      ( r1_tarski(k2_tarski(A_81,B_82),C_83)
      | ~ r2_hidden(B_82,C_83)
      | ~ r2_hidden(A_81,C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_354,plain,(
    ! [A_84,C_85] :
      ( r1_tarski(k1_tarski(A_84),C_85)
      | ~ r2_hidden(A_84,C_85)
      | ~ r2_hidden(A_84,C_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_337])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_39,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_363,plain,(
    ! [A_86,C_87] :
      ( k2_xboole_0(k1_tarski(A_86),C_87) = C_87
      | ~ r2_hidden(A_86,C_87) ) ),
    inference(resolution,[status(thm)],[c_354,c_39])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_413,plain,(
    ! [C_88,A_89] :
      ( k2_xboole_0(C_88,k1_tarski(A_89)) = C_88
      | ~ r2_hidden(A_89,C_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_2])).

tff(c_36,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_40,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_442,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_40])).

tff(c_468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_442])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.16/0.36  % Computer   : n010.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 10:55:14 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.36  
% 2.28/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.36  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.28/1.36  
% 2.28/1.36  %Foreground sorts:
% 2.28/1.36  
% 2.28/1.36  
% 2.28/1.36  %Background operators:
% 2.28/1.36  
% 2.28/1.36  
% 2.28/1.36  %Foreground operators:
% 2.28/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.28/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.28/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.28/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.28/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.28/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.28/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.28/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.36  
% 2.47/1.37  tff(f_66, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 2.47/1.37  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.47/1.37  tff(f_61, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.47/1.37  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.47/1.37  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.47/1.37  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.47/1.37  tff(c_38, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.47/1.37  tff(c_14, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.47/1.37  tff(c_337, plain, (![A_81, B_82, C_83]: (r1_tarski(k2_tarski(A_81, B_82), C_83) | ~r2_hidden(B_82, C_83) | ~r2_hidden(A_81, C_83))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.47/1.37  tff(c_354, plain, (![A_84, C_85]: (r1_tarski(k1_tarski(A_84), C_85) | ~r2_hidden(A_84, C_85) | ~r2_hidden(A_84, C_85))), inference(superposition, [status(thm), theory('equality')], [c_14, c_337])).
% 2.47/1.37  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.37  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.37  tff(c_39, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.47/1.37  tff(c_363, plain, (![A_86, C_87]: (k2_xboole_0(k1_tarski(A_86), C_87)=C_87 | ~r2_hidden(A_86, C_87))), inference(resolution, [status(thm)], [c_354, c_39])).
% 2.47/1.37  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.47/1.37  tff(c_413, plain, (![C_88, A_89]: (k2_xboole_0(C_88, k1_tarski(A_89))=C_88 | ~r2_hidden(A_89, C_88))), inference(superposition, [status(thm), theory('equality')], [c_363, c_2])).
% 2.47/1.37  tff(c_36, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.47/1.37  tff(c_40, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 2.47/1.37  tff(c_442, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_413, c_40])).
% 2.47/1.37  tff(c_468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_442])).
% 2.47/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.37  
% 2.47/1.37  Inference rules
% 2.47/1.37  ----------------------
% 2.47/1.37  #Ref     : 0
% 2.47/1.37  #Sup     : 109
% 2.47/1.37  #Fact    : 0
% 2.47/1.37  #Define  : 0
% 2.47/1.37  #Split   : 0
% 2.47/1.37  #Chain   : 0
% 2.47/1.37  #Close   : 0
% 2.47/1.37  
% 2.47/1.37  Ordering : KBO
% 2.47/1.37  
% 2.47/1.37  Simplification rules
% 2.47/1.37  ----------------------
% 2.47/1.37  #Subsume      : 5
% 2.47/1.37  #Demod        : 23
% 2.47/1.37  #Tautology    : 44
% 2.47/1.37  #SimpNegUnit  : 0
% 2.47/1.37  #BackRed      : 0
% 2.47/1.37  
% 2.47/1.37  #Partial instantiations: 0
% 2.47/1.37  #Strategies tried      : 1
% 2.47/1.37  
% 2.47/1.37  Timing (in seconds)
% 2.47/1.37  ----------------------
% 2.47/1.37  Preprocessing        : 0.32
% 2.47/1.37  Parsing              : 0.18
% 2.47/1.37  CNF conversion       : 0.02
% 2.47/1.37  Main loop            : 0.22
% 2.47/1.37  Inferencing          : 0.08
% 2.47/1.37  Reduction            : 0.08
% 2.47/1.37  Demodulation         : 0.07
% 2.47/1.37  BG Simplification    : 0.02
% 2.47/1.37  Subsumption          : 0.03
% 2.47/1.37  Abstraction          : 0.02
% 2.47/1.37  MUC search           : 0.00
% 2.47/1.37  Cooper               : 0.00
% 2.47/1.37  Total                : 0.57
% 2.47/1.37  Index Insertion      : 0.00
% 2.47/1.37  Index Deletion       : 0.00
% 2.47/1.37  Index Matching       : 0.00
% 2.47/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
