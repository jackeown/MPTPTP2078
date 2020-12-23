%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:55 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :   39 (  50 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   23 (  34 expanded)
%              Number of equality atoms :   22 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_4,plain,(
    ! [A_4,B_5,D_7,C_6] : k2_enumset1(A_4,B_5,D_7,C_6) = k2_enumset1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [C_3,B_2,A_1] : k1_enumset1(C_3,B_2,A_1) = k1_enumset1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_39,B_40,C_41,D_42] : k3_enumset1(A_39,A_39,B_40,C_41,D_42) = k2_enumset1(A_39,B_40,C_41,D_42) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_36,B_37,C_38] : k2_enumset1(A_36,A_36,B_37,C_38) = k1_enumset1(A_36,B_37,C_38) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_710,plain,(
    ! [E_108,C_110,D_109,A_107,B_106] : k2_xboole_0(k2_enumset1(A_107,B_106,C_110,D_109),k1_tarski(E_108)) = k3_enumset1(A_107,B_106,C_110,D_109,E_108) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_740,plain,(
    ! [A_36,B_37,C_38,E_108] : k3_enumset1(A_36,A_36,B_37,C_38,E_108) = k2_xboole_0(k1_enumset1(A_36,B_37,C_38),k1_tarski(E_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_710])).

tff(c_1603,plain,(
    ! [A_157,B_158,C_159,E_160] : k2_xboole_0(k1_enumset1(A_157,B_158,C_159),k1_tarski(E_160)) = k2_enumset1(A_157,B_158,C_159,E_160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_740])).

tff(c_1753,plain,(
    ! [A_174,B_175,C_176,E_177] : k2_xboole_0(k1_enumset1(A_174,B_175,C_176),k1_tarski(E_177)) = k2_enumset1(C_176,B_175,A_174,E_177) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1603])).

tff(c_744,plain,(
    ! [A_36,B_37,C_38,E_108] : k2_xboole_0(k1_enumset1(A_36,B_37,C_38),k1_tarski(E_108)) = k2_enumset1(A_36,B_37,C_38,E_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_740])).

tff(c_1759,plain,(
    ! [C_176,B_175,A_174,E_177] : k2_enumset1(C_176,B_175,A_174,E_177) = k2_enumset1(A_174,B_175,C_176,E_177) ),
    inference(superposition,[status(thm),theory(equality)],[c_1753,c_744])).

tff(c_6,plain,(
    ! [A_8,C_10,D_11,B_9] : k2_enumset1(A_8,C_10,D_11,B_9) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_29,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_28])).

tff(c_30,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_29])).

tff(c_2448,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1759,c_30])).

tff(c_2451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2448])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.62  
% 3.59/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.62  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.59/1.62  
% 3.59/1.62  %Foreground sorts:
% 3.59/1.62  
% 3.59/1.62  
% 3.59/1.62  %Background operators:
% 3.59/1.62  
% 3.59/1.62  
% 3.59/1.62  %Foreground operators:
% 3.59/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.59/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.59/1.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.59/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.59/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.59/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.59/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.59/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.59/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.59/1.62  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.59/1.62  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.59/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.59/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.59/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.59/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.59/1.62  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.59/1.62  
% 3.98/1.63  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 3.98/1.63  tff(f_27, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_enumset1)).
% 3.98/1.63  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.98/1.63  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.98/1.63  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 3.98/1.63  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 3.98/1.63  tff(f_54, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_enumset1)).
% 3.98/1.63  tff(c_4, plain, (![A_4, B_5, D_7, C_6]: (k2_enumset1(A_4, B_5, D_7, C_6)=k2_enumset1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.98/1.63  tff(c_2, plain, (![C_3, B_2, A_1]: (k1_enumset1(C_3, B_2, A_1)=k1_enumset1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.98/1.63  tff(c_20, plain, (![A_39, B_40, C_41, D_42]: (k3_enumset1(A_39, A_39, B_40, C_41, D_42)=k2_enumset1(A_39, B_40, C_41, D_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.98/1.63  tff(c_18, plain, (![A_36, B_37, C_38]: (k2_enumset1(A_36, A_36, B_37, C_38)=k1_enumset1(A_36, B_37, C_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.98/1.63  tff(c_710, plain, (![E_108, C_110, D_109, A_107, B_106]: (k2_xboole_0(k2_enumset1(A_107, B_106, C_110, D_109), k1_tarski(E_108))=k3_enumset1(A_107, B_106, C_110, D_109, E_108))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.63  tff(c_740, plain, (![A_36, B_37, C_38, E_108]: (k3_enumset1(A_36, A_36, B_37, C_38, E_108)=k2_xboole_0(k1_enumset1(A_36, B_37, C_38), k1_tarski(E_108)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_710])).
% 3.98/1.63  tff(c_1603, plain, (![A_157, B_158, C_159, E_160]: (k2_xboole_0(k1_enumset1(A_157, B_158, C_159), k1_tarski(E_160))=k2_enumset1(A_157, B_158, C_159, E_160))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_740])).
% 3.98/1.63  tff(c_1753, plain, (![A_174, B_175, C_176, E_177]: (k2_xboole_0(k1_enumset1(A_174, B_175, C_176), k1_tarski(E_177))=k2_enumset1(C_176, B_175, A_174, E_177))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1603])).
% 3.98/1.63  tff(c_744, plain, (![A_36, B_37, C_38, E_108]: (k2_xboole_0(k1_enumset1(A_36, B_37, C_38), k1_tarski(E_108))=k2_enumset1(A_36, B_37, C_38, E_108))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_740])).
% 3.98/1.63  tff(c_1759, plain, (![C_176, B_175, A_174, E_177]: (k2_enumset1(C_176, B_175, A_174, E_177)=k2_enumset1(A_174, B_175, C_176, E_177))), inference(superposition, [status(thm), theory('equality')], [c_1753, c_744])).
% 3.98/1.63  tff(c_6, plain, (![A_8, C_10, D_11, B_9]: (k2_enumset1(A_8, C_10, D_11, B_9)=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.98/1.63  tff(c_28, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.98/1.63  tff(c_29, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_28])).
% 3.98/1.63  tff(c_30, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_29])).
% 3.98/1.63  tff(c_2448, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1759, c_30])).
% 3.98/1.63  tff(c_2451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_2448])).
% 3.98/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.63  
% 3.98/1.63  Inference rules
% 3.98/1.63  ----------------------
% 3.98/1.63  #Ref     : 0
% 3.98/1.63  #Sup     : 606
% 3.98/1.63  #Fact    : 0
% 3.98/1.63  #Define  : 0
% 3.98/1.63  #Split   : 0
% 3.98/1.63  #Chain   : 0
% 3.98/1.63  #Close   : 0
% 3.98/1.63  
% 3.98/1.63  Ordering : KBO
% 3.98/1.63  
% 3.98/1.63  Simplification rules
% 3.98/1.63  ----------------------
% 3.98/1.63  #Subsume      : 122
% 3.98/1.63  #Demod        : 370
% 3.98/1.63  #Tautology    : 356
% 3.98/1.63  #SimpNegUnit  : 0
% 3.98/1.63  #BackRed      : 1
% 3.98/1.63  
% 3.98/1.63  #Partial instantiations: 0
% 3.98/1.63  #Strategies tried      : 1
% 3.98/1.63  
% 3.98/1.63  Timing (in seconds)
% 3.98/1.63  ----------------------
% 3.98/1.63  Preprocessing        : 0.29
% 3.98/1.63  Parsing              : 0.16
% 3.98/1.63  CNF conversion       : 0.02
% 3.98/1.63  Main loop            : 0.58
% 3.98/1.63  Inferencing          : 0.19
% 3.98/1.63  Reduction            : 0.27
% 3.98/1.63  Demodulation         : 0.23
% 3.98/1.63  BG Simplification    : 0.03
% 3.98/1.63  Subsumption          : 0.07
% 3.98/1.63  Abstraction          : 0.04
% 3.98/1.63  MUC search           : 0.00
% 3.98/1.63  Cooper               : 0.00
% 3.98/1.63  Total                : 0.90
% 3.98/1.63  Index Insertion      : 0.00
% 3.98/1.63  Index Deletion       : 0.00
% 3.98/1.63  Index Matching       : 0.00
% 3.98/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
