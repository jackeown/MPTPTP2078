%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:38 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   39 (  55 expanded)
%              Number of leaves         :   25 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  38 expanded)
%              Number of equality atoms :   21 (  37 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_270,plain,(
    ! [A_55,B_56] : k5_xboole_0(A_55,k3_xboole_0(A_55,B_56)) = k4_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_291,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_270])).

tff(c_297,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_291])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_79,plain,(
    ! [A_41,B_42] : k3_xboole_0(A_41,k2_xboole_0(A_41,B_42)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k1_xboole_0) = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_79])).

tff(c_91,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_88])).

tff(c_177,plain,(
    ! [B_49] : k4_xboole_0(k1_tarski(B_49),k1_tarski(B_49)) != k1_tarski(B_49) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_180,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_177])).

tff(c_184,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_91,c_180])).

tff(c_301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 14:43:30 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.17  
% 1.95/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.17  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.95/1.17  
% 1.95/1.17  %Foreground sorts:
% 1.95/1.17  
% 1.95/1.17  
% 1.95/1.17  %Background operators:
% 1.95/1.17  
% 1.95/1.17  
% 1.95/1.17  %Foreground operators:
% 1.95/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.95/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.95/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.95/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.95/1.17  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.17  
% 1.95/1.18  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.95/1.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.95/1.18  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.95/1.18  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.95/1.18  tff(f_60, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.95/1.18  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.95/1.18  tff(f_56, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.95/1.18  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.95/1.18  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.95/1.18  tff(c_270, plain, (![A_55, B_56]: (k5_xboole_0(A_55, k3_xboole_0(A_55, B_56))=k4_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.18  tff(c_291, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_270])).
% 1.95/1.18  tff(c_297, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_291])).
% 1.95/1.18  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.18  tff(c_32, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.95/1.18  tff(c_79, plain, (![A_41, B_42]: (k3_xboole_0(A_41, k2_xboole_0(A_41, B_42))=A_41)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.18  tff(c_88, plain, (k3_xboole_0(k1_tarski('#skF_1'), k1_xboole_0)=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_79])).
% 1.95/1.18  tff(c_91, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_88])).
% 1.95/1.18  tff(c_177, plain, (![B_49]: (k4_xboole_0(k1_tarski(B_49), k1_tarski(B_49))!=k1_tarski(B_49))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.95/1.18  tff(c_180, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_91, c_177])).
% 1.95/1.18  tff(c_184, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_91, c_91, c_180])).
% 1.95/1.18  tff(c_301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_297, c_184])).
% 1.95/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.18  
% 1.95/1.18  Inference rules
% 1.95/1.18  ----------------------
% 1.95/1.18  #Ref     : 0
% 1.95/1.18  #Sup     : 69
% 1.95/1.18  #Fact    : 0
% 1.95/1.18  #Define  : 0
% 1.95/1.18  #Split   : 0
% 1.95/1.18  #Chain   : 0
% 1.95/1.18  #Close   : 0
% 1.95/1.18  
% 1.95/1.18  Ordering : KBO
% 1.95/1.18  
% 1.95/1.18  Simplification rules
% 1.95/1.18  ----------------------
% 1.95/1.18  #Subsume      : 1
% 1.95/1.18  #Demod        : 23
% 1.95/1.18  #Tautology    : 53
% 1.95/1.18  #SimpNegUnit  : 0
% 1.95/1.18  #BackRed      : 3
% 1.95/1.18  
% 1.95/1.18  #Partial instantiations: 0
% 1.95/1.18  #Strategies tried      : 1
% 1.95/1.18  
% 1.95/1.18  Timing (in seconds)
% 1.95/1.18  ----------------------
% 1.95/1.18  Preprocessing        : 0.30
% 1.95/1.18  Parsing              : 0.16
% 1.95/1.18  CNF conversion       : 0.02
% 1.95/1.18  Main loop            : 0.14
% 1.95/1.18  Inferencing          : 0.05
% 1.95/1.18  Reduction            : 0.05
% 1.95/1.18  Demodulation         : 0.04
% 1.95/1.18  BG Simplification    : 0.01
% 1.95/1.18  Subsumption          : 0.02
% 1.95/1.18  Abstraction          : 0.01
% 1.95/1.18  MUC search           : 0.00
% 1.95/1.18  Cooper               : 0.00
% 1.95/1.18  Total                : 0.46
% 1.95/1.18  Index Insertion      : 0.00
% 1.95/1.18  Index Deletion       : 0.00
% 1.95/1.18  Index Matching       : 0.00
% 1.95/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
