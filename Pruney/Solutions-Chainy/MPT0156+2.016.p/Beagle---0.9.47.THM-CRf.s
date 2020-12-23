%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:16 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_xboole_0(k1_tarski(A_1),k1_enumset1(B_2,C_3,D_4)) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_63,plain,(
    ! [B_28,E_29,A_30,D_31,C_32] : k2_xboole_0(k2_tarski(A_30,B_28),k1_enumset1(C_32,D_31,E_29)) = k3_enumset1(A_30,B_28,C_32,D_31,E_29) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_15,C_32,D_31,E_29] : k3_enumset1(A_15,A_15,C_32,D_31,E_29) = k2_xboole_0(k1_tarski(A_15),k1_enumset1(C_32,D_31,E_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_63])).

tff(c_78,plain,(
    ! [A_15,C_32,D_31,E_29] : k3_enumset1(A_15,A_15,C_32,D_31,E_29) = k2_enumset1(A_15,C_32,D_31,E_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_75])).

tff(c_12,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:32:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.16  
% 1.68/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.16  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.68/1.16  
% 1.68/1.16  %Foreground sorts:
% 1.68/1.16  
% 1.68/1.16  
% 1.68/1.16  %Background operators:
% 1.68/1.16  
% 1.68/1.16  
% 1.68/1.16  %Foreground operators:
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.68/1.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.68/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.68/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.68/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.68/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.68/1.16  
% 1.68/1.17  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 1.68/1.17  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.68/1.17  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 1.68/1.17  tff(f_38, negated_conjecture, ~(![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.68/1.17  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k1_tarski(A_1), k1_enumset1(B_2, C_3, D_4))=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.68/1.17  tff(c_8, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.68/1.17  tff(c_63, plain, (![B_28, E_29, A_30, D_31, C_32]: (k2_xboole_0(k2_tarski(A_30, B_28), k1_enumset1(C_32, D_31, E_29))=k3_enumset1(A_30, B_28, C_32, D_31, E_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.17  tff(c_75, plain, (![A_15, C_32, D_31, E_29]: (k3_enumset1(A_15, A_15, C_32, D_31, E_29)=k2_xboole_0(k1_tarski(A_15), k1_enumset1(C_32, D_31, E_29)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_63])).
% 1.68/1.17  tff(c_78, plain, (![A_15, C_32, D_31, E_29]: (k3_enumset1(A_15, A_15, C_32, D_31, E_29)=k2_enumset1(A_15, C_32, D_31, E_29))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_75])).
% 1.68/1.17  tff(c_12, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.68/1.17  tff(c_107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_12])).
% 1.68/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.17  
% 1.68/1.17  Inference rules
% 1.68/1.17  ----------------------
% 1.68/1.17  #Ref     : 0
% 1.68/1.17  #Sup     : 22
% 1.68/1.17  #Fact    : 0
% 1.68/1.17  #Define  : 0
% 1.68/1.17  #Split   : 0
% 1.68/1.17  #Chain   : 0
% 1.68/1.17  #Close   : 0
% 1.68/1.17  
% 1.68/1.17  Ordering : KBO
% 1.68/1.17  
% 1.68/1.17  Simplification rules
% 1.68/1.17  ----------------------
% 1.68/1.17  #Subsume      : 0
% 1.68/1.17  #Demod        : 4
% 1.68/1.17  #Tautology    : 18
% 1.68/1.17  #SimpNegUnit  : 0
% 1.68/1.17  #BackRed      : 1
% 1.68/1.17  
% 1.68/1.17  #Partial instantiations: 0
% 1.68/1.17  #Strategies tried      : 1
% 1.68/1.17  
% 1.68/1.17  Timing (in seconds)
% 1.68/1.17  ----------------------
% 1.68/1.17  Preprocessing        : 0.26
% 1.68/1.17  Parsing              : 0.13
% 1.68/1.17  CNF conversion       : 0.01
% 1.68/1.17  Main loop            : 0.09
% 1.68/1.18  Inferencing          : 0.04
% 1.68/1.18  Reduction            : 0.03
% 1.68/1.18  Demodulation         : 0.03
% 1.68/1.18  BG Simplification    : 0.01
% 1.68/1.18  Subsumption          : 0.01
% 1.68/1.18  Abstraction          : 0.01
% 1.68/1.18  MUC search           : 0.00
% 1.68/1.18  Cooper               : 0.00
% 1.68/1.18  Total                : 0.37
% 1.68/1.18  Index Insertion      : 0.00
% 1.68/1.18  Index Deletion       : 0.00
% 1.68/1.18  Index Matching       : 0.00
% 1.68/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
