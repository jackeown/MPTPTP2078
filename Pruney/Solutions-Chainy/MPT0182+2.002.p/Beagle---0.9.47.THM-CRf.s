%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:42 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_36,B_37,C_38] : k2_enumset1(A_36,A_36,B_37,C_38) = k1_enumset1(A_36,B_37,C_38) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_34,B_35] : k1_enumset1(A_34,A_34,B_35) = k2_tarski(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_39,B_40,C_41,D_42] : k3_enumset1(A_39,A_39,B_40,C_41,D_42) = k2_enumset1(A_39,B_40,C_41,D_42) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_127,plain,(
    ! [B_83,D_84,E_85,C_82,A_86] : k2_xboole_0(k2_enumset1(A_86,B_83,C_82,D_84),k1_tarski(E_85)) = k3_enumset1(A_86,B_83,C_82,D_84,E_85) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [A_36,B_37,C_38,E_85] : k3_enumset1(A_36,A_36,B_37,C_38,E_85) = k2_xboole_0(k1_enumset1(A_36,B_37,C_38),k1_tarski(E_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_127])).

tff(c_140,plain,(
    ! [A_87,B_88,C_89,E_90] : k2_xboole_0(k1_enumset1(A_87,B_88,C_89),k1_tarski(E_90)) = k2_enumset1(A_87,B_88,C_89,E_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_136])).

tff(c_149,plain,(
    ! [A_34,B_35,E_90] : k2_xboole_0(k2_tarski(A_34,B_35),k1_tarski(E_90)) = k2_enumset1(A_34,A_34,B_35,E_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_140])).

tff(c_153,plain,(
    ! [A_91,B_92,E_93] : k2_xboole_0(k2_tarski(A_91,B_92),k1_tarski(E_93)) = k1_enumset1(A_91,B_92,E_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_149])).

tff(c_181,plain,(
    ! [B_96,A_97,E_98] : k2_xboole_0(k2_tarski(B_96,A_97),k1_tarski(E_98)) = k1_enumset1(A_97,B_96,E_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_153])).

tff(c_152,plain,(
    ! [A_34,B_35,E_90] : k2_xboole_0(k2_tarski(A_34,B_35),k1_tarski(E_90)) = k1_enumset1(A_34,B_35,E_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_149])).

tff(c_187,plain,(
    ! [B_96,A_97,E_98] : k1_enumset1(B_96,A_97,E_98) = k1_enumset1(A_97,B_96,E_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_152])).

tff(c_30,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:13:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.25  
% 2.03/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.25  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.03/1.25  
% 2.03/1.25  %Foreground sorts:
% 2.03/1.25  
% 2.03/1.25  
% 2.03/1.25  %Background operators:
% 2.03/1.25  
% 2.03/1.25  
% 2.03/1.25  %Foreground operators:
% 2.03/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.03/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.03/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.03/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.25  
% 2.03/1.26  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.03/1.26  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.03/1.26  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.03/1.26  tff(f_47, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.03/1.26  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 2.03/1.26  tff(f_56, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_enumset1)).
% 2.03/1.26  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.26  tff(c_20, plain, (![A_36, B_37, C_38]: (k2_enumset1(A_36, A_36, B_37, C_38)=k1_enumset1(A_36, B_37, C_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.03/1.26  tff(c_18, plain, (![A_34, B_35]: (k1_enumset1(A_34, A_34, B_35)=k2_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.03/1.26  tff(c_22, plain, (![A_39, B_40, C_41, D_42]: (k3_enumset1(A_39, A_39, B_40, C_41, D_42)=k2_enumset1(A_39, B_40, C_41, D_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.03/1.26  tff(c_127, plain, (![B_83, D_84, E_85, C_82, A_86]: (k2_xboole_0(k2_enumset1(A_86, B_83, C_82, D_84), k1_tarski(E_85))=k3_enumset1(A_86, B_83, C_82, D_84, E_85))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.03/1.26  tff(c_136, plain, (![A_36, B_37, C_38, E_85]: (k3_enumset1(A_36, A_36, B_37, C_38, E_85)=k2_xboole_0(k1_enumset1(A_36, B_37, C_38), k1_tarski(E_85)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_127])).
% 2.03/1.26  tff(c_140, plain, (![A_87, B_88, C_89, E_90]: (k2_xboole_0(k1_enumset1(A_87, B_88, C_89), k1_tarski(E_90))=k2_enumset1(A_87, B_88, C_89, E_90))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_136])).
% 2.03/1.26  tff(c_149, plain, (![A_34, B_35, E_90]: (k2_xboole_0(k2_tarski(A_34, B_35), k1_tarski(E_90))=k2_enumset1(A_34, A_34, B_35, E_90))), inference(superposition, [status(thm), theory('equality')], [c_18, c_140])).
% 2.03/1.26  tff(c_153, plain, (![A_91, B_92, E_93]: (k2_xboole_0(k2_tarski(A_91, B_92), k1_tarski(E_93))=k1_enumset1(A_91, B_92, E_93))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_149])).
% 2.03/1.26  tff(c_181, plain, (![B_96, A_97, E_98]: (k2_xboole_0(k2_tarski(B_96, A_97), k1_tarski(E_98))=k1_enumset1(A_97, B_96, E_98))), inference(superposition, [status(thm), theory('equality')], [c_6, c_153])).
% 2.03/1.26  tff(c_152, plain, (![A_34, B_35, E_90]: (k2_xboole_0(k2_tarski(A_34, B_35), k1_tarski(E_90))=k1_enumset1(A_34, B_35, E_90))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_149])).
% 2.03/1.26  tff(c_187, plain, (![B_96, A_97, E_98]: (k1_enumset1(B_96, A_97, E_98)=k1_enumset1(A_97, B_96, E_98))), inference(superposition, [status(thm), theory('equality')], [c_181, c_152])).
% 2.03/1.26  tff(c_30, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.03/1.26  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_187, c_30])).
% 2.03/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.26  
% 2.03/1.26  Inference rules
% 2.03/1.26  ----------------------
% 2.03/1.26  #Ref     : 0
% 2.03/1.26  #Sup     : 42
% 2.03/1.26  #Fact    : 0
% 2.03/1.26  #Define  : 0
% 2.03/1.26  #Split   : 0
% 2.03/1.26  #Chain   : 0
% 2.03/1.26  #Close   : 0
% 2.03/1.26  
% 2.03/1.26  Ordering : KBO
% 2.03/1.26  
% 2.03/1.26  Simplification rules
% 2.03/1.26  ----------------------
% 2.03/1.26  #Subsume      : 0
% 2.03/1.26  #Demod        : 8
% 2.03/1.26  #Tautology    : 35
% 2.03/1.26  #SimpNegUnit  : 0
% 2.03/1.26  #BackRed      : 1
% 2.03/1.26  
% 2.03/1.26  #Partial instantiations: 0
% 2.03/1.26  #Strategies tried      : 1
% 2.03/1.26  
% 2.03/1.26  Timing (in seconds)
% 2.03/1.26  ----------------------
% 2.03/1.26  Preprocessing        : 0.31
% 2.03/1.26  Parsing              : 0.17
% 2.03/1.26  CNF conversion       : 0.02
% 2.03/1.26  Main loop            : 0.13
% 2.03/1.26  Inferencing          : 0.05
% 2.03/1.26  Reduction            : 0.05
% 2.03/1.26  Demodulation         : 0.04
% 2.03/1.26  BG Simplification    : 0.01
% 2.03/1.26  Subsumption          : 0.02
% 2.03/1.26  Abstraction          : 0.01
% 2.03/1.26  MUC search           : 0.00
% 2.03/1.26  Cooper               : 0.00
% 2.03/1.26  Total                : 0.47
% 2.03/1.26  Index Insertion      : 0.00
% 2.03/1.26  Index Deletion       : 0.00
% 2.03/1.26  Index Matching       : 0.00
% 2.03/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
