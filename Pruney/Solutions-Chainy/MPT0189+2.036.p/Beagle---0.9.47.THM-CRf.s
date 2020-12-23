%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:55 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   32 (  39 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   16 (  23 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :   10 (   5 average)
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

tff(f_45,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_20,plain,(
    ! [B_43,A_42,C_44] : k1_enumset1(B_43,A_42,C_44) = k1_enumset1(A_42,B_43,C_44) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_20,B_21,C_22,D_23] : k3_enumset1(A_20,A_20,B_21,C_22,D_23) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_17,B_18,C_19] : k2_enumset1(A_17,A_17,B_18,C_19) = k1_enumset1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,(
    ! [D_64,A_67,E_63,C_66,B_65] : k2_xboole_0(k2_enumset1(A_67,B_65,C_66,D_64),k1_tarski(E_63)) = k3_enumset1(A_67,B_65,C_66,D_64,E_63) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_110,plain,(
    ! [A_17,B_18,C_19,E_63] : k3_enumset1(A_17,A_17,B_18,C_19,E_63) = k2_xboole_0(k1_enumset1(A_17,B_18,C_19),k1_tarski(E_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_101])).

tff(c_114,plain,(
    ! [A_68,B_69,C_70,E_71] : k2_xboole_0(k1_enumset1(A_68,B_69,C_70),k1_tarski(E_71)) = k2_enumset1(A_68,B_69,C_70,E_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_110])).

tff(c_164,plain,(
    ! [A_83,B_84,C_85,E_86] : k2_xboole_0(k1_enumset1(A_83,B_84,C_85),k1_tarski(E_86)) = k2_enumset1(B_84,A_83,C_85,E_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_114])).

tff(c_113,plain,(
    ! [A_17,B_18,C_19,E_63] : k2_xboole_0(k1_enumset1(A_17,B_18,C_19),k1_tarski(E_63)) = k2_enumset1(A_17,B_18,C_19,E_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_110])).

tff(c_170,plain,(
    ! [B_84,A_83,C_85,E_86] : k2_enumset1(B_84,A_83,C_85,E_86) = k2_enumset1(A_83,B_84,C_85,E_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_113])).

tff(c_22,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:03:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.33  
% 1.88/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.33  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.88/1.33  
% 1.88/1.33  %Foreground sorts:
% 1.88/1.33  
% 1.88/1.33  
% 1.88/1.33  %Background operators:
% 1.88/1.33  
% 1.88/1.33  
% 1.88/1.33  %Foreground operators:
% 1.88/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.88/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.88/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.88/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.88/1.33  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.33  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.33  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.88/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.88/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.33  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.88/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.88/1.33  
% 1.88/1.34  tff(f_45, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_enumset1)).
% 1.88/1.34  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.88/1.34  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.88/1.34  tff(f_27, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 1.88/1.34  tff(f_48, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 1.88/1.34  tff(c_20, plain, (![B_43, A_42, C_44]: (k1_enumset1(B_43, A_42, C_44)=k1_enumset1(A_42, B_43, C_44))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.88/1.34  tff(c_12, plain, (![A_20, B_21, C_22, D_23]: (k3_enumset1(A_20, A_20, B_21, C_22, D_23)=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.88/1.34  tff(c_10, plain, (![A_17, B_18, C_19]: (k2_enumset1(A_17, A_17, B_18, C_19)=k1_enumset1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.88/1.34  tff(c_101, plain, (![D_64, A_67, E_63, C_66, B_65]: (k2_xboole_0(k2_enumset1(A_67, B_65, C_66, D_64), k1_tarski(E_63))=k3_enumset1(A_67, B_65, C_66, D_64, E_63))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.88/1.34  tff(c_110, plain, (![A_17, B_18, C_19, E_63]: (k3_enumset1(A_17, A_17, B_18, C_19, E_63)=k2_xboole_0(k1_enumset1(A_17, B_18, C_19), k1_tarski(E_63)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_101])).
% 1.88/1.34  tff(c_114, plain, (![A_68, B_69, C_70, E_71]: (k2_xboole_0(k1_enumset1(A_68, B_69, C_70), k1_tarski(E_71))=k2_enumset1(A_68, B_69, C_70, E_71))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_110])).
% 1.88/1.34  tff(c_164, plain, (![A_83, B_84, C_85, E_86]: (k2_xboole_0(k1_enumset1(A_83, B_84, C_85), k1_tarski(E_86))=k2_enumset1(B_84, A_83, C_85, E_86))), inference(superposition, [status(thm), theory('equality')], [c_20, c_114])).
% 1.88/1.34  tff(c_113, plain, (![A_17, B_18, C_19, E_63]: (k2_xboole_0(k1_enumset1(A_17, B_18, C_19), k1_tarski(E_63))=k2_enumset1(A_17, B_18, C_19, E_63))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_110])).
% 1.88/1.34  tff(c_170, plain, (![B_84, A_83, C_85, E_86]: (k2_enumset1(B_84, A_83, C_85, E_86)=k2_enumset1(A_83, B_84, C_85, E_86))), inference(superposition, [status(thm), theory('equality')], [c_164, c_113])).
% 1.88/1.34  tff(c_22, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.88/1.34  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_170, c_22])).
% 1.88/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.34  
% 1.88/1.34  Inference rules
% 1.88/1.34  ----------------------
% 1.88/1.34  #Ref     : 0
% 1.88/1.34  #Sup     : 40
% 1.88/1.34  #Fact    : 0
% 1.88/1.34  #Define  : 0
% 1.88/1.34  #Split   : 0
% 1.88/1.34  #Chain   : 0
% 1.88/1.34  #Close   : 0
% 1.88/1.34  
% 1.88/1.34  Ordering : KBO
% 1.88/1.34  
% 1.88/1.34  Simplification rules
% 2.12/1.34  ----------------------
% 2.12/1.34  #Subsume      : 0
% 2.12/1.34  #Demod        : 8
% 2.12/1.34  #Tautology    : 33
% 2.12/1.34  #SimpNegUnit  : 0
% 2.12/1.34  #BackRed      : 1
% 2.12/1.34  
% 2.12/1.34  #Partial instantiations: 0
% 2.12/1.34  #Strategies tried      : 1
% 2.12/1.34  
% 2.12/1.34  Timing (in seconds)
% 2.12/1.34  ----------------------
% 2.12/1.34  Preprocessing        : 0.41
% 2.12/1.34  Parsing              : 0.22
% 2.12/1.34  CNF conversion       : 0.02
% 2.12/1.34  Main loop            : 0.13
% 2.12/1.34  Inferencing          : 0.06
% 2.12/1.34  Reduction            : 0.05
% 2.12/1.34  Demodulation         : 0.04
% 2.12/1.34  BG Simplification    : 0.02
% 2.12/1.34  Subsumption          : 0.02
% 2.12/1.34  Abstraction          : 0.01
% 2.12/1.34  MUC search           : 0.00
% 2.12/1.34  Cooper               : 0.00
% 2.12/1.34  Total                : 0.56
% 2.12/1.34  Index Insertion      : 0.00
% 2.12/1.34  Index Deletion       : 0.00
% 2.12/1.34  Index Matching       : 0.00
% 2.12/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
