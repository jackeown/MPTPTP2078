%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:52 EST 2020

% Result     : Theorem 4.17s
% Output     : CNFRefutation 4.17s
% Verified   : 
% Statistics : Number of formulae       :   42 (  52 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  33 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_55,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_12,plain,(
    ! [A_16,C_18,D_19,B_17] : k2_enumset1(A_16,C_18,D_19,B_17) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    ! [A_80,B_81,C_82,D_83] : k3_enumset1(A_80,A_80,B_81,C_82,D_83) = k2_enumset1(A_80,B_81,C_82,D_83) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    ! [A_75,B_76] : k1_enumset1(A_75,A_75,B_76) = k2_tarski(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_700,plain,(
    ! [E_155,B_152,A_154,D_151,C_153] : k2_xboole_0(k1_enumset1(A_154,B_152,C_153),k2_tarski(D_151,E_155)) = k3_enumset1(A_154,B_152,C_153,D_151,E_155) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_724,plain,(
    ! [A_75,B_76,D_151,E_155] : k3_enumset1(A_75,A_75,B_76,D_151,E_155) = k2_xboole_0(k2_tarski(A_75,B_76),k2_tarski(D_151,E_155)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_700])).

tff(c_736,plain,(
    ! [A_75,B_76,D_151,E_155] : k2_xboole_0(k2_tarski(A_75,B_76),k2_tarski(D_151,E_155)) = k2_enumset1(A_75,B_76,D_151,E_155) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_724])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2227,plain,(
    ! [E_266,A_269,B_267,D_265,C_268] : k2_xboole_0(k2_tarski(D_265,E_266),k1_enumset1(A_269,B_267,C_268)) = k3_enumset1(A_269,B_267,C_268,D_265,E_266) ),
    inference(superposition,[status(thm),theory(equality)],[c_700,c_2])).

tff(c_2266,plain,(
    ! [A_75,B_76,D_265,E_266] : k3_enumset1(A_75,A_75,B_76,D_265,E_266) = k2_xboole_0(k2_tarski(D_265,E_266),k2_tarski(A_75,B_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2227])).

tff(c_2282,plain,(
    ! [D_265,E_266,A_75,B_76] : k2_enumset1(D_265,E_266,A_75,B_76) = k2_enumset1(A_75,B_76,D_265,E_266) ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_34,c_2266])).

tff(c_10,plain,(
    ! [A_12,B_13,D_15,C_14] : k2_enumset1(A_12,B_13,D_15,C_14) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_43,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_42])).

tff(c_44,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_43])).

tff(c_2291,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2282,c_44])).

tff(c_2294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2291])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:36:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.17/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.17/1.79  
% 4.17/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.17/1.79  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.17/1.79  
% 4.17/1.79  %Foreground sorts:
% 4.17/1.79  
% 4.17/1.79  
% 4.17/1.79  %Background operators:
% 4.17/1.79  
% 4.17/1.79  
% 4.17/1.79  %Foreground operators:
% 4.17/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.17/1.79  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.17/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.17/1.79  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.17/1.79  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.17/1.79  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.17/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.17/1.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.17/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.17/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.17/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.17/1.79  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.17/1.79  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.17/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.17/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.17/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.17/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.17/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.17/1.79  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.17/1.79  
% 4.17/1.80  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 4.17/1.80  tff(f_59, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.17/1.80  tff(f_55, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.17/1.80  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 4.17/1.80  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.17/1.80  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 4.17/1.80  tff(f_68, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 4.17/1.80  tff(c_12, plain, (![A_16, C_18, D_19, B_17]: (k2_enumset1(A_16, C_18, D_19, B_17)=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.17/1.80  tff(c_34, plain, (![A_80, B_81, C_82, D_83]: (k3_enumset1(A_80, A_80, B_81, C_82, D_83)=k2_enumset1(A_80, B_81, C_82, D_83))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.17/1.80  tff(c_30, plain, (![A_75, B_76]: (k1_enumset1(A_75, A_75, B_76)=k2_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.17/1.80  tff(c_700, plain, (![E_155, B_152, A_154, D_151, C_153]: (k2_xboole_0(k1_enumset1(A_154, B_152, C_153), k2_tarski(D_151, E_155))=k3_enumset1(A_154, B_152, C_153, D_151, E_155))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.17/1.80  tff(c_724, plain, (![A_75, B_76, D_151, E_155]: (k3_enumset1(A_75, A_75, B_76, D_151, E_155)=k2_xboole_0(k2_tarski(A_75, B_76), k2_tarski(D_151, E_155)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_700])).
% 4.17/1.80  tff(c_736, plain, (![A_75, B_76, D_151, E_155]: (k2_xboole_0(k2_tarski(A_75, B_76), k2_tarski(D_151, E_155))=k2_enumset1(A_75, B_76, D_151, E_155))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_724])).
% 4.17/1.80  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.17/1.80  tff(c_2227, plain, (![E_266, A_269, B_267, D_265, C_268]: (k2_xboole_0(k2_tarski(D_265, E_266), k1_enumset1(A_269, B_267, C_268))=k3_enumset1(A_269, B_267, C_268, D_265, E_266))), inference(superposition, [status(thm), theory('equality')], [c_700, c_2])).
% 4.17/1.80  tff(c_2266, plain, (![A_75, B_76, D_265, E_266]: (k3_enumset1(A_75, A_75, B_76, D_265, E_266)=k2_xboole_0(k2_tarski(D_265, E_266), k2_tarski(A_75, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2227])).
% 4.17/1.80  tff(c_2282, plain, (![D_265, E_266, A_75, B_76]: (k2_enumset1(D_265, E_266, A_75, B_76)=k2_enumset1(A_75, B_76, D_265, E_266))), inference(demodulation, [status(thm), theory('equality')], [c_736, c_34, c_2266])).
% 4.17/1.80  tff(c_10, plain, (![A_12, B_13, D_15, C_14]: (k2_enumset1(A_12, B_13, D_15, C_14)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.17/1.80  tff(c_42, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.17/1.80  tff(c_43, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_42])).
% 4.17/1.80  tff(c_44, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_43])).
% 4.17/1.80  tff(c_2291, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2282, c_44])).
% 4.17/1.80  tff(c_2294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2291])).
% 4.17/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.17/1.80  
% 4.17/1.80  Inference rules
% 4.17/1.80  ----------------------
% 4.17/1.80  #Ref     : 0
% 4.17/1.80  #Sup     : 560
% 4.17/1.80  #Fact    : 0
% 4.17/1.80  #Define  : 0
% 4.17/1.80  #Split   : 0
% 4.17/1.80  #Chain   : 0
% 4.17/1.80  #Close   : 0
% 4.17/1.80  
% 4.17/1.80  Ordering : KBO
% 4.17/1.80  
% 4.17/1.80  Simplification rules
% 4.17/1.80  ----------------------
% 4.17/1.80  #Subsume      : 100
% 4.17/1.80  #Demod        : 321
% 4.17/1.80  #Tautology    : 342
% 4.17/1.80  #SimpNegUnit  : 0
% 4.17/1.80  #BackRed      : 1
% 4.17/1.80  
% 4.17/1.80  #Partial instantiations: 0
% 4.17/1.80  #Strategies tried      : 1
% 4.17/1.80  
% 4.17/1.80  Timing (in seconds)
% 4.17/1.80  ----------------------
% 4.17/1.81  Preprocessing        : 0.42
% 4.17/1.81  Parsing              : 0.21
% 4.17/1.81  CNF conversion       : 0.03
% 4.17/1.81  Main loop            : 0.58
% 4.17/1.81  Inferencing          : 0.20
% 4.17/1.81  Reduction            : 0.26
% 4.17/1.81  Demodulation         : 0.22
% 4.17/1.81  BG Simplification    : 0.04
% 4.17/1.81  Subsumption          : 0.07
% 4.17/1.81  Abstraction          : 0.04
% 4.17/1.81  MUC search           : 0.00
% 4.17/1.81  Cooper               : 0.00
% 4.17/1.81  Total                : 1.02
% 4.17/1.81  Index Insertion      : 0.00
% 4.17/1.81  Index Deletion       : 0.00
% 4.17/1.81  Index Matching       : 0.00
% 4.17/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
