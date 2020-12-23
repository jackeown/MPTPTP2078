%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:28 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   40 (  53 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   35 (  49 expanded)
%              Number of equality atoms :   34 (  48 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_129,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_144,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_129])).

tff(c_147,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_144])).

tff(c_18,plain,(
    ! [B_16] : k4_xboole_0(k1_tarski(B_16),k1_tarski(B_16)) != k1_tarski(B_16) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_148,plain,(
    ! [B_16] : k1_tarski(B_16) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_18])).

tff(c_24,plain,(
    ! [A_19] : k1_setfam_1(k1_tarski(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(k1_tarski(A_5),k1_tarski(B_6)) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_248,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(k1_setfam_1(A_45),k1_setfam_1(B_46)) = k1_setfam_1(k2_xboole_0(A_45,B_46))
      | k1_xboole_0 = B_46
      | k1_xboole_0 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_268,plain,(
    ! [A_45,A_19] :
      ( k1_setfam_1(k2_xboole_0(A_45,k1_tarski(A_19))) = k3_xboole_0(k1_setfam_1(A_45),A_19)
      | k1_tarski(A_19) = k1_xboole_0
      | k1_xboole_0 = A_45 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_248])).

tff(c_348,plain,(
    ! [A_51,A_52] :
      ( k1_setfam_1(k2_xboole_0(A_51,k1_tarski(A_52))) = k3_xboole_0(k1_setfam_1(A_51),A_52)
      | k1_xboole_0 = A_51 ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_268])).

tff(c_371,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_5)),B_6) = k1_setfam_1(k2_tarski(A_5,B_6))
      | k1_tarski(A_5) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_348])).

tff(c_382,plain,(
    ! [A_5,B_6] :
      ( k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6)
      | k1_tarski(A_5) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_371])).

tff(c_383,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_382])).

tff(c_26,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:52:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.29  
% 2.07/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.29  %$ k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.07/1.29  
% 2.07/1.29  %Foreground sorts:
% 2.07/1.29  
% 2.07/1.29  
% 2.07/1.29  %Background operators:
% 2.07/1.29  
% 2.07/1.29  
% 2.07/1.29  %Foreground operators:
% 2.07/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.07/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.07/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.07/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.07/1.29  
% 2.07/1.30  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.07/1.30  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.07/1.30  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.07/1.30  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.07/1.30  tff(f_58, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.07/1.30  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.07/1.30  tff(f_56, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.07/1.30  tff(f_61, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.07/1.30  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.30  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.30  tff(c_129, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.30  tff(c_144, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_129])).
% 2.07/1.30  tff(c_147, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_144])).
% 2.07/1.30  tff(c_18, plain, (![B_16]: (k4_xboole_0(k1_tarski(B_16), k1_tarski(B_16))!=k1_tarski(B_16))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.07/1.30  tff(c_148, plain, (![B_16]: (k1_tarski(B_16)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_18])).
% 2.07/1.30  tff(c_24, plain, (![A_19]: (k1_setfam_1(k1_tarski(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.07/1.30  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(B_6))=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.30  tff(c_248, plain, (![A_45, B_46]: (k3_xboole_0(k1_setfam_1(A_45), k1_setfam_1(B_46))=k1_setfam_1(k2_xboole_0(A_45, B_46)) | k1_xboole_0=B_46 | k1_xboole_0=A_45)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.07/1.30  tff(c_268, plain, (![A_45, A_19]: (k1_setfam_1(k2_xboole_0(A_45, k1_tarski(A_19)))=k3_xboole_0(k1_setfam_1(A_45), A_19) | k1_tarski(A_19)=k1_xboole_0 | k1_xboole_0=A_45)), inference(superposition, [status(thm), theory('equality')], [c_24, c_248])).
% 2.07/1.30  tff(c_348, plain, (![A_51, A_52]: (k1_setfam_1(k2_xboole_0(A_51, k1_tarski(A_52)))=k3_xboole_0(k1_setfam_1(A_51), A_52) | k1_xboole_0=A_51)), inference(negUnitSimplification, [status(thm)], [c_148, c_268])).
% 2.07/1.30  tff(c_371, plain, (![A_5, B_6]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_5)), B_6)=k1_setfam_1(k2_tarski(A_5, B_6)) | k1_tarski(A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_348])).
% 2.07/1.30  tff(c_382, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6) | k1_tarski(A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_371])).
% 2.07/1.30  tff(c_383, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(negUnitSimplification, [status(thm)], [c_148, c_382])).
% 2.07/1.30  tff(c_26, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.07/1.30  tff(c_388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_383, c_26])).
% 2.07/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.30  
% 2.07/1.30  Inference rules
% 2.07/1.30  ----------------------
% 2.07/1.30  #Ref     : 0
% 2.07/1.30  #Sup     : 81
% 2.07/1.30  #Fact    : 0
% 2.07/1.30  #Define  : 0
% 2.07/1.30  #Split   : 0
% 2.07/1.30  #Chain   : 0
% 2.07/1.30  #Close   : 0
% 2.07/1.30  
% 2.07/1.30  Ordering : KBO
% 2.07/1.30  
% 2.07/1.30  Simplification rules
% 2.07/1.30  ----------------------
% 2.07/1.30  #Subsume      : 2
% 2.07/1.30  #Demod        : 32
% 2.07/1.30  #Tautology    : 59
% 2.07/1.30  #SimpNegUnit  : 12
% 2.07/1.30  #BackRed      : 2
% 2.07/1.30  
% 2.07/1.30  #Partial instantiations: 0
% 2.07/1.30  #Strategies tried      : 1
% 2.07/1.30  
% 2.07/1.30  Timing (in seconds)
% 2.07/1.30  ----------------------
% 2.07/1.30  Preprocessing        : 0.28
% 2.07/1.30  Parsing              : 0.15
% 2.07/1.30  CNF conversion       : 0.02
% 2.07/1.30  Main loop            : 0.19
% 2.07/1.30  Inferencing          : 0.08
% 2.07/1.30  Reduction            : 0.06
% 2.07/1.30  Demodulation         : 0.05
% 2.07/1.30  BG Simplification    : 0.01
% 2.07/1.30  Subsumption          : 0.03
% 2.07/1.30  Abstraction          : 0.01
% 2.07/1.30  MUC search           : 0.00
% 2.07/1.30  Cooper               : 0.00
% 2.07/1.30  Total                : 0.49
% 2.07/1.30  Index Insertion      : 0.00
% 2.07/1.30  Index Deletion       : 0.00
% 2.07/1.30  Index Matching       : 0.00
% 2.07/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
