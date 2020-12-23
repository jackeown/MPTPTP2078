%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:24 EST 2020

% Result     : Theorem 16.85s
% Output     : CNFRefutation 16.95s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_81,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_89,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_85,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_enumset1)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] : k3_enumset1(A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

tff(c_54,plain,(
    ! [A_58,B_59,C_60] : k2_xboole_0(k1_tarski(A_58),k2_tarski(B_59,C_60)) = k1_enumset1(A_58,B_59,C_60) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_62,plain,(
    ! [A_71] : k1_enumset1(A_71,A_71,A_71) = k1_tarski(A_71) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5883,plain,(
    ! [C_215,E_217,A_216,B_214,D_213] : k2_xboole_0(k1_enumset1(A_216,B_214,C_215),k2_tarski(D_213,E_217)) = k3_enumset1(A_216,B_214,C_215,D_213,E_217) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_5955,plain,(
    ! [A_71,D_213,E_217] : k3_enumset1(A_71,A_71,A_71,D_213,E_217) = k2_xboole_0(k1_tarski(A_71),k2_tarski(D_213,E_217)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_5883])).

tff(c_5965,plain,(
    ! [A_71,D_213,E_217] : k3_enumset1(A_71,A_71,A_71,D_213,E_217) = k1_enumset1(A_71,D_213,E_217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5955])).

tff(c_64,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_54510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5965,c_64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:54:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.85/8.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.85/8.97  
% 16.85/8.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.85/8.97  %$ r1_xboole_0 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 16.85/8.97  
% 16.85/8.97  %Foreground sorts:
% 16.85/8.97  
% 16.85/8.97  
% 16.85/8.97  %Background operators:
% 16.85/8.97  
% 16.85/8.97  
% 16.85/8.97  %Foreground operators:
% 16.85/8.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.85/8.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.85/8.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.85/8.97  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 16.85/8.97  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 16.85/8.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.85/8.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.85/8.97  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.85/8.97  tff('#skF_2', type, '#skF_2': $i).
% 16.85/8.97  tff('#skF_3', type, '#skF_3': $i).
% 16.85/8.97  tff('#skF_1', type, '#skF_1': $i).
% 16.85/8.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.85/8.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.85/8.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.85/8.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.85/8.97  
% 16.95/8.97  tff(f_81, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 16.95/8.97  tff(f_89, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 16.95/8.97  tff(f_85, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_enumset1)).
% 16.95/8.97  tff(f_92, negated_conjecture, ~(![A, B, C]: (k3_enumset1(A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_enumset1)).
% 16.95/8.97  tff(c_54, plain, (![A_58, B_59, C_60]: (k2_xboole_0(k1_tarski(A_58), k2_tarski(B_59, C_60))=k1_enumset1(A_58, B_59, C_60))), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.95/8.97  tff(c_62, plain, (![A_71]: (k1_enumset1(A_71, A_71, A_71)=k1_tarski(A_71))), inference(cnfTransformation, [status(thm)], [f_89])).
% 16.95/8.97  tff(c_5883, plain, (![C_215, E_217, A_216, B_214, D_213]: (k2_xboole_0(k1_enumset1(A_216, B_214, C_215), k2_tarski(D_213, E_217))=k3_enumset1(A_216, B_214, C_215, D_213, E_217))), inference(cnfTransformation, [status(thm)], [f_85])).
% 16.95/8.97  tff(c_5955, plain, (![A_71, D_213, E_217]: (k3_enumset1(A_71, A_71, A_71, D_213, E_217)=k2_xboole_0(k1_tarski(A_71), k2_tarski(D_213, E_217)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_5883])).
% 16.95/8.97  tff(c_5965, plain, (![A_71, D_213, E_217]: (k3_enumset1(A_71, A_71, A_71, D_213, E_217)=k1_enumset1(A_71, D_213, E_217))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5955])).
% 16.95/8.97  tff(c_64, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 16.95/8.97  tff(c_54510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5965, c_64])).
% 16.95/8.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.95/8.97  
% 16.95/8.97  Inference rules
% 16.95/8.97  ----------------------
% 16.95/8.97  #Ref     : 0
% 16.95/8.97  #Sup     : 14015
% 16.95/8.97  #Fact    : 0
% 16.95/8.97  #Define  : 0
% 16.95/8.97  #Split   : 0
% 16.95/8.97  #Chain   : 0
% 16.95/8.98  #Close   : 0
% 16.95/8.98  
% 16.95/8.98  Ordering : KBO
% 16.95/8.98  
% 16.95/8.98  Simplification rules
% 16.95/8.98  ----------------------
% 16.95/8.98  #Subsume      : 1497
% 16.95/8.98  #Demod        : 16632
% 16.95/8.98  #Tautology    : 6374
% 16.95/8.98  #SimpNegUnit  : 0
% 16.95/8.98  #BackRed      : 11
% 16.95/8.98  
% 16.95/8.98  #Partial instantiations: 0
% 16.95/8.98  #Strategies tried      : 1
% 16.95/8.98  
% 16.95/8.98  Timing (in seconds)
% 16.95/8.98  ----------------------
% 16.95/8.98  Preprocessing        : 0.33
% 16.95/8.98  Parsing              : 0.17
% 16.95/8.98  CNF conversion       : 0.02
% 16.95/8.98  Main loop            : 7.87
% 16.95/8.98  Inferencing          : 1.19
% 16.95/8.98  Reduction            : 4.92
% 16.95/8.98  Demodulation         : 4.55
% 16.95/8.98  BG Simplification    : 0.17
% 16.95/8.98  Subsumption          : 1.21
% 16.95/8.98  Abstraction          : 0.32
% 16.95/8.98  MUC search           : 0.00
% 16.95/8.98  Cooper               : 0.00
% 16.95/8.98  Total                : 8.22
% 16.95/8.98  Index Insertion      : 0.00
% 16.95/8.98  Index Deletion       : 0.00
% 16.95/8.98  Index Matching       : 0.00
% 16.95/8.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
