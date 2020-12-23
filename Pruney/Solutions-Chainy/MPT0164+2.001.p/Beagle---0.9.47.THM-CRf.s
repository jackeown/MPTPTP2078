%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:24 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k5_enumset1(A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_enumset1)).

tff(c_4,plain,(
    ! [B_6,C_7,E_9,D_8,A_5] : k2_xboole_0(k1_tarski(A_5),k2_enumset1(B_6,C_7,D_8,E_9)) = k3_enumset1(A_5,B_6,C_7,D_8,E_9) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_170,plain,(
    ! [A_46,G_43,F_48,C_49,E_45,D_47,B_44] : k2_xboole_0(k1_enumset1(A_46,B_44,C_49),k2_enumset1(D_47,E_45,F_48,G_43)) = k5_enumset1(A_46,B_44,C_49,D_47,E_45,F_48,G_43) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_267,plain,(
    ! [B_62,A_60,D_59,E_58,F_61,G_63] : k5_enumset1(A_60,A_60,B_62,D_59,E_58,F_61,G_63) = k2_xboole_0(k2_tarski(A_60,B_62),k2_enumset1(D_59,E_58,F_61,G_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_170])).

tff(c_291,plain,(
    ! [D_59,E_58,F_61,A_17,G_63] : k5_enumset1(A_17,A_17,A_17,D_59,E_58,F_61,G_63) = k2_xboole_0(k1_tarski(A_17),k2_enumset1(D_59,E_58,F_61,G_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_267])).

tff(c_296,plain,(
    ! [D_59,E_58,F_61,A_17,G_63] : k5_enumset1(A_17,A_17,A_17,D_59,E_58,F_61,G_63) = k3_enumset1(A_17,D_59,E_58,F_61,G_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_291])).

tff(c_12,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:42:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.21  
% 1.95/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.21  %$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.95/1.21  
% 1.95/1.21  %Foreground sorts:
% 1.95/1.21  
% 1.95/1.21  
% 1.95/1.21  %Background operators:
% 1.95/1.21  
% 1.95/1.21  
% 1.95/1.21  %Foreground operators:
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.95/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.95/1.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.21  
% 2.06/1.22  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 2.06/1.22  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.06/1.22  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.06/1.22  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 2.06/1.22  tff(f_38, negated_conjecture, ~(![A, B, C, D, E]: (k5_enumset1(A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_enumset1)).
% 2.06/1.22  tff(c_4, plain, (![B_6, C_7, E_9, D_8, A_5]: (k2_xboole_0(k1_tarski(A_5), k2_enumset1(B_6, C_7, D_8, E_9))=k3_enumset1(A_5, B_6, C_7, D_8, E_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.22  tff(c_8, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.22  tff(c_10, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.22  tff(c_170, plain, (![A_46, G_43, F_48, C_49, E_45, D_47, B_44]: (k2_xboole_0(k1_enumset1(A_46, B_44, C_49), k2_enumset1(D_47, E_45, F_48, G_43))=k5_enumset1(A_46, B_44, C_49, D_47, E_45, F_48, G_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.22  tff(c_267, plain, (![B_62, A_60, D_59, E_58, F_61, G_63]: (k5_enumset1(A_60, A_60, B_62, D_59, E_58, F_61, G_63)=k2_xboole_0(k2_tarski(A_60, B_62), k2_enumset1(D_59, E_58, F_61, G_63)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_170])).
% 2.06/1.22  tff(c_291, plain, (![D_59, E_58, F_61, A_17, G_63]: (k5_enumset1(A_17, A_17, A_17, D_59, E_58, F_61, G_63)=k2_xboole_0(k1_tarski(A_17), k2_enumset1(D_59, E_58, F_61, G_63)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_267])).
% 2.06/1.22  tff(c_296, plain, (![D_59, E_58, F_61, A_17, G_63]: (k5_enumset1(A_17, A_17, A_17, D_59, E_58, F_61, G_63)=k3_enumset1(A_17, D_59, E_58, F_61, G_63))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_291])).
% 2.06/1.22  tff(c_12, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.22  tff(c_299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_296, c_12])).
% 2.06/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.22  
% 2.06/1.22  Inference rules
% 2.06/1.22  ----------------------
% 2.06/1.22  #Ref     : 0
% 2.06/1.22  #Sup     : 70
% 2.06/1.22  #Fact    : 0
% 2.06/1.22  #Define  : 0
% 2.06/1.22  #Split   : 0
% 2.06/1.22  #Chain   : 0
% 2.06/1.22  #Close   : 0
% 2.06/1.22  
% 2.06/1.22  Ordering : KBO
% 2.06/1.22  
% 2.06/1.22  Simplification rules
% 2.06/1.22  ----------------------
% 2.06/1.22  #Subsume      : 3
% 2.06/1.22  #Demod        : 21
% 2.06/1.22  #Tautology    : 53
% 2.06/1.22  #SimpNegUnit  : 0
% 2.06/1.22  #BackRed      : 1
% 2.06/1.22  
% 2.06/1.22  #Partial instantiations: 0
% 2.06/1.22  #Strategies tried      : 1
% 2.06/1.22  
% 2.06/1.22  Timing (in seconds)
% 2.06/1.22  ----------------------
% 2.06/1.22  Preprocessing        : 0.27
% 2.06/1.22  Parsing              : 0.15
% 2.06/1.22  CNF conversion       : 0.01
% 2.06/1.22  Main loop            : 0.19
% 2.06/1.22  Inferencing          : 0.09
% 2.06/1.22  Reduction            : 0.07
% 2.06/1.22  Demodulation         : 0.06
% 2.06/1.22  BG Simplification    : 0.01
% 2.06/1.22  Subsumption          : 0.02
% 2.06/1.22  Abstraction          : 0.01
% 2.06/1.22  MUC search           : 0.00
% 2.06/1.22  Cooper               : 0.00
% 2.06/1.22  Total                : 0.48
% 2.06/1.22  Index Insertion      : 0.00
% 2.06/1.22  Index Deletion       : 0.00
% 2.06/1.22  Index Matching       : 0.00
% 2.06/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
