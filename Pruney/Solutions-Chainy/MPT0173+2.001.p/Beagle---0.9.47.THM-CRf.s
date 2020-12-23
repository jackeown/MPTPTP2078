%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:31 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   36 (  38 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] : k5_enumset1(A,A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_enumset1)).

tff(c_10,plain,(
    ! [A_16,B_17,C_18] : k2_enumset1(A_16,A_16,B_17,C_18) = k1_enumset1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_xboole_0(k1_tarski(A_3),k1_enumset1(B_4,C_5,D_6)) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ! [A_25,B_26] : k1_enumset1(A_25,A_25,B_26) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_23] : k1_enumset1(A_23,A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_33,plain,(
    ! [B_26] : k2_tarski(B_26,B_26) = k1_tarski(B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_14])).

tff(c_12,plain,(
    ! [A_19,B_20,C_21,D_22] : k3_enumset1(A_19,A_19,B_20,C_21,D_22) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_214,plain,(
    ! [B_49,D_48,F_53,E_54,C_50,A_51,G_52] : k2_xboole_0(k2_tarski(A_51,B_49),k3_enumset1(C_50,D_48,E_54,F_53,G_52)) = k5_enumset1(A_51,B_49,C_50,D_48,E_54,F_53,G_52) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_296,plain,(
    ! [B_62,A_60,D_64,A_63,B_61,C_59] : k5_enumset1(A_60,B_61,A_63,A_63,B_62,C_59,D_64) = k2_xboole_0(k2_tarski(A_60,B_61),k2_enumset1(A_63,B_62,C_59,D_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_214])).

tff(c_446,plain,(
    ! [A_74,B_73,C_75,D_72,B_71] : k5_enumset1(B_71,B_71,A_74,A_74,B_73,C_75,D_72) = k2_xboole_0(k1_tarski(B_71),k2_enumset1(A_74,B_73,C_75,D_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_296])).

tff(c_502,plain,(
    ! [B_71,A_16,B_17,C_18] : k5_enumset1(B_71,B_71,A_16,A_16,A_16,B_17,C_18) = k2_xboole_0(k1_tarski(B_71),k1_enumset1(A_16,B_17,C_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_446])).

tff(c_515,plain,(
    ! [B_71,A_16,B_17,C_18] : k5_enumset1(B_71,B_71,A_16,A_16,A_16,B_17,C_18) = k2_enumset1(B_71,A_16,B_17,C_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_502])).

tff(c_16,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_516,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_16])).

tff(c_519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_516])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.28  
% 2.22/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.28  %$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.22/1.28  
% 2.22/1.28  %Foreground sorts:
% 2.22/1.28  
% 2.22/1.28  
% 2.22/1.28  %Background operators:
% 2.22/1.28  
% 2.22/1.28  
% 2.22/1.28  %Foreground operators:
% 2.22/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.22/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.22/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.22/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.22/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.22/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.28  
% 2.22/1.29  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.22/1.29  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 2.22/1.29  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.22/1.29  tff(f_39, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 2.22/1.29  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.22/1.29  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_enumset1)).
% 2.22/1.29  tff(f_42, negated_conjecture, ~(![A, B, C]: (k5_enumset1(A, A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_enumset1)).
% 2.22/1.29  tff(c_10, plain, (![A_16, B_17, C_18]: (k2_enumset1(A_16, A_16, B_17, C_18)=k1_enumset1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.29  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (k2_xboole_0(k1_tarski(A_3), k1_enumset1(B_4, C_5, D_6))=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.29  tff(c_26, plain, (![A_25, B_26]: (k1_enumset1(A_25, A_25, B_26)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.22/1.29  tff(c_14, plain, (![A_23]: (k1_enumset1(A_23, A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.22/1.29  tff(c_33, plain, (![B_26]: (k2_tarski(B_26, B_26)=k1_tarski(B_26))), inference(superposition, [status(thm), theory('equality')], [c_26, c_14])).
% 2.22/1.29  tff(c_12, plain, (![A_19, B_20, C_21, D_22]: (k3_enumset1(A_19, A_19, B_20, C_21, D_22)=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.22/1.29  tff(c_214, plain, (![B_49, D_48, F_53, E_54, C_50, A_51, G_52]: (k2_xboole_0(k2_tarski(A_51, B_49), k3_enumset1(C_50, D_48, E_54, F_53, G_52))=k5_enumset1(A_51, B_49, C_50, D_48, E_54, F_53, G_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.29  tff(c_296, plain, (![B_62, A_60, D_64, A_63, B_61, C_59]: (k5_enumset1(A_60, B_61, A_63, A_63, B_62, C_59, D_64)=k2_xboole_0(k2_tarski(A_60, B_61), k2_enumset1(A_63, B_62, C_59, D_64)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_214])).
% 2.22/1.29  tff(c_446, plain, (![A_74, B_73, C_75, D_72, B_71]: (k5_enumset1(B_71, B_71, A_74, A_74, B_73, C_75, D_72)=k2_xboole_0(k1_tarski(B_71), k2_enumset1(A_74, B_73, C_75, D_72)))), inference(superposition, [status(thm), theory('equality')], [c_33, c_296])).
% 2.22/1.29  tff(c_502, plain, (![B_71, A_16, B_17, C_18]: (k5_enumset1(B_71, B_71, A_16, A_16, A_16, B_17, C_18)=k2_xboole_0(k1_tarski(B_71), k1_enumset1(A_16, B_17, C_18)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_446])).
% 2.22/1.29  tff(c_515, plain, (![B_71, A_16, B_17, C_18]: (k5_enumset1(B_71, B_71, A_16, A_16, A_16, B_17, C_18)=k2_enumset1(B_71, A_16, B_17, C_18))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_502])).
% 2.22/1.29  tff(c_16, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.22/1.29  tff(c_516, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_515, c_16])).
% 2.22/1.29  tff(c_519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_516])).
% 2.22/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.29  
% 2.22/1.29  Inference rules
% 2.22/1.29  ----------------------
% 2.22/1.29  #Ref     : 0
% 2.22/1.29  #Sup     : 118
% 2.22/1.29  #Fact    : 0
% 2.22/1.29  #Define  : 0
% 2.22/1.29  #Split   : 0
% 2.22/1.29  #Chain   : 0
% 2.22/1.29  #Close   : 0
% 2.22/1.29  
% 2.22/1.29  Ordering : KBO
% 2.22/1.29  
% 2.22/1.29  Simplification rules
% 2.22/1.29  ----------------------
% 2.22/1.29  #Subsume      : 2
% 2.22/1.29  #Demod        : 79
% 2.22/1.29  #Tautology    : 93
% 2.22/1.29  #SimpNegUnit  : 0
% 2.22/1.29  #BackRed      : 1
% 2.22/1.29  
% 2.22/1.29  #Partial instantiations: 0
% 2.22/1.29  #Strategies tried      : 1
% 2.22/1.29  
% 2.22/1.29  Timing (in seconds)
% 2.22/1.29  ----------------------
% 2.22/1.29  Preprocessing        : 0.28
% 2.22/1.29  Parsing              : 0.14
% 2.22/1.29  CNF conversion       : 0.02
% 2.22/1.29  Main loop            : 0.25
% 2.22/1.29  Inferencing          : 0.12
% 2.22/1.29  Reduction            : 0.09
% 2.22/1.29  Demodulation         : 0.08
% 2.22/1.29  BG Simplification    : 0.01
% 2.22/1.29  Subsumption          : 0.02
% 2.22/1.29  Abstraction          : 0.02
% 2.22/1.29  MUC search           : 0.00
% 2.22/1.29  Cooper               : 0.00
% 2.22/1.29  Total                : 0.55
% 2.22/1.29  Index Insertion      : 0.00
% 2.22/1.29  Index Deletion       : 0.00
% 2.22/1.29  Index Matching       : 0.00
% 2.22/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
