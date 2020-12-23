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
% DateTime   : Thu Dec  3 09:46:43 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   38 (  53 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   20 (  35 expanded)
%              Number of equality atoms :   19 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_37,B_38,C_39] : k2_enumset1(A_37,A_37,B_38,C_39) = k1_enumset1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_35,B_36] : k1_enumset1(A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_40,B_41,C_42,D_43] : k3_enumset1(A_40,A_40,B_41,C_42,D_43) = k2_enumset1(A_40,B_41,C_42,D_43) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_127,plain,(
    ! [A_87,D_84,C_83,B_85,E_86] : k2_xboole_0(k2_enumset1(A_87,B_85,C_83,D_84),k1_tarski(E_86)) = k3_enumset1(A_87,B_85,C_83,D_84,E_86) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_136,plain,(
    ! [A_37,B_38,C_39,E_86] : k3_enumset1(A_37,A_37,B_38,C_39,E_86) = k2_xboole_0(k1_enumset1(A_37,B_38,C_39),k1_tarski(E_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_127])).

tff(c_140,plain,(
    ! [A_88,B_89,C_90,E_91] : k2_xboole_0(k1_enumset1(A_88,B_89,C_90),k1_tarski(E_91)) = k2_enumset1(A_88,B_89,C_90,E_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_136])).

tff(c_149,plain,(
    ! [A_35,B_36,E_91] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(E_91)) = k2_enumset1(A_35,A_35,B_36,E_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_140])).

tff(c_153,plain,(
    ! [A_92,B_93,E_94] : k2_xboole_0(k2_tarski(A_92,B_93),k1_tarski(E_94)) = k1_enumset1(A_92,B_93,E_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_149])).

tff(c_181,plain,(
    ! [B_97,A_98,E_99] : k2_xboole_0(k2_tarski(B_97,A_98),k1_tarski(E_99)) = k1_enumset1(A_98,B_97,E_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_153])).

tff(c_152,plain,(
    ! [A_35,B_36,E_91] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(E_91)) = k1_enumset1(A_35,B_36,E_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_149])).

tff(c_187,plain,(
    ! [B_97,A_98,E_99] : k1_enumset1(B_97,A_98,E_99) = k1_enumset1(A_98,B_97,E_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_152])).

tff(c_30,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.19  
% 1.94/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.19  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.94/1.19  
% 1.94/1.19  %Foreground sorts:
% 1.94/1.19  
% 1.94/1.19  
% 1.94/1.19  %Background operators:
% 1.94/1.19  
% 1.94/1.19  
% 1.94/1.19  %Foreground operators:
% 1.94/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.94/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.94/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.94/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.94/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.94/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.94/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.94/1.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.94/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.94/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.94/1.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.94/1.19  
% 1.94/1.20  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.94/1.20  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.94/1.20  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.94/1.20  tff(f_47, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.94/1.20  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 1.94/1.20  tff(f_56, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_enumset1)).
% 1.94/1.20  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.20  tff(c_20, plain, (![A_37, B_38, C_39]: (k2_enumset1(A_37, A_37, B_38, C_39)=k1_enumset1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.20  tff(c_18, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.94/1.20  tff(c_22, plain, (![A_40, B_41, C_42, D_43]: (k3_enumset1(A_40, A_40, B_41, C_42, D_43)=k2_enumset1(A_40, B_41, C_42, D_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.94/1.20  tff(c_127, plain, (![A_87, D_84, C_83, B_85, E_86]: (k2_xboole_0(k2_enumset1(A_87, B_85, C_83, D_84), k1_tarski(E_86))=k3_enumset1(A_87, B_85, C_83, D_84, E_86))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.20  tff(c_136, plain, (![A_37, B_38, C_39, E_86]: (k3_enumset1(A_37, A_37, B_38, C_39, E_86)=k2_xboole_0(k1_enumset1(A_37, B_38, C_39), k1_tarski(E_86)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_127])).
% 1.94/1.20  tff(c_140, plain, (![A_88, B_89, C_90, E_91]: (k2_xboole_0(k1_enumset1(A_88, B_89, C_90), k1_tarski(E_91))=k2_enumset1(A_88, B_89, C_90, E_91))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_136])).
% 1.94/1.20  tff(c_149, plain, (![A_35, B_36, E_91]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(E_91))=k2_enumset1(A_35, A_35, B_36, E_91))), inference(superposition, [status(thm), theory('equality')], [c_18, c_140])).
% 1.94/1.20  tff(c_153, plain, (![A_92, B_93, E_94]: (k2_xboole_0(k2_tarski(A_92, B_93), k1_tarski(E_94))=k1_enumset1(A_92, B_93, E_94))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_149])).
% 1.94/1.20  tff(c_181, plain, (![B_97, A_98, E_99]: (k2_xboole_0(k2_tarski(B_97, A_98), k1_tarski(E_99))=k1_enumset1(A_98, B_97, E_99))), inference(superposition, [status(thm), theory('equality')], [c_6, c_153])).
% 1.94/1.20  tff(c_152, plain, (![A_35, B_36, E_91]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(E_91))=k1_enumset1(A_35, B_36, E_91))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_149])).
% 1.94/1.20  tff(c_187, plain, (![B_97, A_98, E_99]: (k1_enumset1(B_97, A_98, E_99)=k1_enumset1(A_98, B_97, E_99))), inference(superposition, [status(thm), theory('equality')], [c_181, c_152])).
% 1.94/1.20  tff(c_30, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.94/1.20  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_187, c_30])).
% 1.94/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.20  
% 1.94/1.20  Inference rules
% 1.94/1.20  ----------------------
% 1.94/1.20  #Ref     : 0
% 1.94/1.20  #Sup     : 42
% 1.94/1.20  #Fact    : 0
% 1.94/1.20  #Define  : 0
% 1.94/1.20  #Split   : 0
% 1.94/1.20  #Chain   : 0
% 1.94/1.20  #Close   : 0
% 1.94/1.20  
% 1.94/1.20  Ordering : KBO
% 1.94/1.20  
% 1.94/1.20  Simplification rules
% 1.94/1.20  ----------------------
% 1.94/1.20  #Subsume      : 0
% 1.94/1.20  #Demod        : 8
% 1.94/1.20  #Tautology    : 35
% 1.94/1.20  #SimpNegUnit  : 0
% 1.94/1.20  #BackRed      : 1
% 1.94/1.20  
% 1.94/1.20  #Partial instantiations: 0
% 1.94/1.20  #Strategies tried      : 1
% 1.94/1.20  
% 1.94/1.20  Timing (in seconds)
% 1.94/1.20  ----------------------
% 1.94/1.21  Preprocessing        : 0.31
% 1.94/1.21  Parsing              : 0.17
% 1.94/1.21  CNF conversion       : 0.02
% 1.94/1.21  Main loop            : 0.14
% 1.94/1.21  Inferencing          : 0.05
% 1.94/1.21  Reduction            : 0.05
% 1.94/1.21  Demodulation         : 0.04
% 1.94/1.21  BG Simplification    : 0.01
% 1.94/1.21  Subsumption          : 0.02
% 1.94/1.21  Abstraction          : 0.01
% 1.94/1.21  MUC search           : 0.00
% 1.94/1.21  Cooper               : 0.00
% 1.94/1.21  Total                : 0.47
% 1.94/1.21  Index Insertion      : 0.00
% 1.94/1.21  Index Deletion       : 0.00
% 1.94/1.21  Index Matching       : 0.00
% 1.94/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
