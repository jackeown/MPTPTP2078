%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:28 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   33 (  43 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   31 (  41 expanded)
%              Number of equality atoms :   30 (  40 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_46,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_37,plain,(
    ! [A_19,B_20] : k2_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    ! [A_14,B_15,C_16] : k2_xboole_0(k2_tarski(A_14,B_15),C_16) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_35,plain,(
    ! [A_5,C_16] : k2_xboole_0(k1_tarski(A_5),C_16) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_33])).

tff(c_44,plain,(
    ! [A_5] : k1_tarski(A_5) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_35])).

tff(c_12,plain,(
    ! [A_11] : k1_setfam_1(k1_tarski(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k1_tarski(A_3),k1_tarski(B_4)) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(k1_setfam_1(A_26),k1_setfam_1(B_27)) = k1_setfam_1(k2_xboole_0(A_26,B_27))
      | k1_xboole_0 = B_27
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_81,plain,(
    ! [A_11,B_27] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_11),B_27)) = k3_xboole_0(A_11,k1_setfam_1(B_27))
      | k1_xboole_0 = B_27
      | k1_tarski(A_11) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_69])).

tff(c_89,plain,(
    ! [A_28,B_29] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_28),B_29)) = k3_xboole_0(A_28,k1_setfam_1(B_29))
      | k1_xboole_0 = B_29 ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_81])).

tff(c_104,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,k1_setfam_1(k1_tarski(B_4))) = k1_setfam_1(k2_tarski(A_3,B_4))
      | k1_tarski(B_4) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_89])).

tff(c_113,plain,(
    ! [A_3,B_4] :
      ( k1_setfam_1(k2_tarski(A_3,B_4)) = k3_xboole_0(A_3,B_4)
      | k1_tarski(B_4) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_104])).

tff(c_114,plain,(
    ! [A_3,B_4] : k1_setfam_1(k2_tarski(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_113])).

tff(c_14,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:05:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.15  
% 1.65/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.15  %$ k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.65/1.15  
% 1.65/1.15  %Foreground sorts:
% 1.65/1.15  
% 1.65/1.15  
% 1.65/1.15  %Background operators:
% 1.65/1.15  
% 1.65/1.15  
% 1.65/1.15  %Foreground operators:
% 1.65/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.65/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.65/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.65/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.65/1.15  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.65/1.15  
% 1.65/1.16  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 1.65/1.16  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.65/1.16  tff(f_34, axiom, (![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 1.65/1.16  tff(f_46, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 1.65/1.16  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.65/1.16  tff(f_44, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 1.65/1.16  tff(f_49, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.65/1.16  tff(c_37, plain, (![A_19, B_20]: (k2_xboole_0(A_19, k3_xboole_0(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.65/1.16  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.16  tff(c_33, plain, (![A_14, B_15, C_16]: (k2_xboole_0(k2_tarski(A_14, B_15), C_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.65/1.16  tff(c_35, plain, (![A_5, C_16]: (k2_xboole_0(k1_tarski(A_5), C_16)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_33])).
% 1.65/1.16  tff(c_44, plain, (![A_5]: (k1_tarski(A_5)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_37, c_35])).
% 1.65/1.16  tff(c_12, plain, (![A_11]: (k1_setfam_1(k1_tarski(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.65/1.16  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k1_tarski(A_3), k1_tarski(B_4))=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.16  tff(c_69, plain, (![A_26, B_27]: (k3_xboole_0(k1_setfam_1(A_26), k1_setfam_1(B_27))=k1_setfam_1(k2_xboole_0(A_26, B_27)) | k1_xboole_0=B_27 | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.65/1.16  tff(c_81, plain, (![A_11, B_27]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_11), B_27))=k3_xboole_0(A_11, k1_setfam_1(B_27)) | k1_xboole_0=B_27 | k1_tarski(A_11)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_69])).
% 1.65/1.16  tff(c_89, plain, (![A_28, B_29]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_28), B_29))=k3_xboole_0(A_28, k1_setfam_1(B_29)) | k1_xboole_0=B_29)), inference(negUnitSimplification, [status(thm)], [c_44, c_81])).
% 1.65/1.16  tff(c_104, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k1_setfam_1(k1_tarski(B_4)))=k1_setfam_1(k2_tarski(A_3, B_4)) | k1_tarski(B_4)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_89])).
% 1.65/1.16  tff(c_113, plain, (![A_3, B_4]: (k1_setfam_1(k2_tarski(A_3, B_4))=k3_xboole_0(A_3, B_4) | k1_tarski(B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_104])).
% 1.65/1.16  tff(c_114, plain, (![A_3, B_4]: (k1_setfam_1(k2_tarski(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(negUnitSimplification, [status(thm)], [c_44, c_113])).
% 1.65/1.16  tff(c_14, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.65/1.16  tff(c_118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_14])).
% 1.65/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.16  
% 1.65/1.16  Inference rules
% 1.65/1.16  ----------------------
% 1.65/1.16  #Ref     : 0
% 1.65/1.16  #Sup     : 24
% 1.65/1.16  #Fact    : 0
% 1.65/1.16  #Define  : 0
% 1.65/1.16  #Split   : 0
% 1.65/1.16  #Chain   : 0
% 1.65/1.16  #Close   : 0
% 1.65/1.16  
% 1.65/1.16  Ordering : KBO
% 1.65/1.16  
% 1.65/1.16  Simplification rules
% 1.65/1.16  ----------------------
% 1.65/1.16  #Subsume      : 2
% 1.65/1.16  #Demod        : 3
% 1.65/1.16  #Tautology    : 12
% 1.65/1.16  #SimpNegUnit  : 5
% 1.65/1.16  #BackRed      : 1
% 1.65/1.16  
% 1.65/1.16  #Partial instantiations: 0
% 1.65/1.16  #Strategies tried      : 1
% 1.65/1.16  
% 1.65/1.16  Timing (in seconds)
% 1.65/1.16  ----------------------
% 1.65/1.16  Preprocessing        : 0.28
% 1.65/1.16  Parsing              : 0.15
% 1.65/1.16  CNF conversion       : 0.01
% 1.65/1.16  Main loop            : 0.12
% 1.65/1.16  Inferencing          : 0.05
% 1.65/1.16  Reduction            : 0.03
% 1.65/1.16  Demodulation         : 0.02
% 1.65/1.16  BG Simplification    : 0.01
% 1.65/1.16  Subsumption          : 0.02
% 1.65/1.16  Abstraction          : 0.01
% 1.65/1.16  MUC search           : 0.00
% 1.65/1.16  Cooper               : 0.00
% 1.65/1.16  Total                : 0.42
% 1.65/1.16  Index Insertion      : 0.00
% 1.65/1.16  Index Deletion       : 0.00
% 1.65/1.16  Index Matching       : 0.00
% 1.65/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
