%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:25 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   37 (  47 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  47 expanded)
%              Number of equality atoms :   29 (  38 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [A_30,B_31] :
      ( r1_xboole_0(A_30,B_31)
      | k3_xboole_0(A_30,B_31) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [B_20] : ~ r1_xboole_0(k1_tarski(B_20),k1_tarski(B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_62,plain,(
    ! [B_20] : k3_xboole_0(k1_tarski(B_20),k1_tarski(B_20)) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_20])).

tff(c_65,plain,(
    ! [B_20] : k1_tarski(B_20) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_62])).

tff(c_24,plain,(
    ! [A_23] : k1_setfam_1(k1_tarski(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(k1_tarski(A_5),k1_tarski(B_6)) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_236,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(k1_setfam_1(A_54),k1_setfam_1(B_55)) = k1_setfam_1(k2_xboole_0(A_54,B_55))
      | k1_xboole_0 = B_55
      | k1_xboole_0 = A_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_256,plain,(
    ! [A_54,A_23] :
      ( k1_setfam_1(k2_xboole_0(A_54,k1_tarski(A_23))) = k3_xboole_0(k1_setfam_1(A_54),A_23)
      | k1_tarski(A_23) = k1_xboole_0
      | k1_xboole_0 = A_54 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_236])).

tff(c_478,plain,(
    ! [A_65,A_66] :
      ( k1_setfam_1(k2_xboole_0(A_65,k1_tarski(A_66))) = k3_xboole_0(k1_setfam_1(A_65),A_66)
      | k1_xboole_0 = A_65 ) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_256])).

tff(c_515,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_5)),B_6) = k1_setfam_1(k2_tarski(A_5,B_6))
      | k1_tarski(A_5) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_478])).

tff(c_532,plain,(
    ! [A_5,B_6] :
      ( k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6)
      | k1_tarski(A_5) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_515])).

tff(c_533,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_532])).

tff(c_26,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.41  
% 2.16/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.41  %$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.16/1.41  
% 2.16/1.41  %Foreground sorts:
% 2.16/1.41  
% 2.16/1.41  
% 2.16/1.41  %Background operators:
% 2.16/1.41  
% 2.16/1.41  
% 2.16/1.41  %Foreground operators:
% 2.16/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.16/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.16/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.16/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.16/1.41  
% 2.16/1.42  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.16/1.42  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.16/1.42  tff(f_48, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.16/1.42  tff(f_60, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.16/1.42  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.16/1.42  tff(f_58, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.16/1.42  tff(f_63, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.16/1.42  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.42  tff(c_56, plain, (![A_30, B_31]: (r1_xboole_0(A_30, B_31) | k3_xboole_0(A_30, B_31)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.42  tff(c_20, plain, (![B_20]: (~r1_xboole_0(k1_tarski(B_20), k1_tarski(B_20)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.16/1.42  tff(c_62, plain, (![B_20]: (k3_xboole_0(k1_tarski(B_20), k1_tarski(B_20))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_20])).
% 2.16/1.42  tff(c_65, plain, (![B_20]: (k1_tarski(B_20)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_62])).
% 2.16/1.42  tff(c_24, plain, (![A_23]: (k1_setfam_1(k1_tarski(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.16/1.42  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(B_6))=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.42  tff(c_236, plain, (![A_54, B_55]: (k3_xboole_0(k1_setfam_1(A_54), k1_setfam_1(B_55))=k1_setfam_1(k2_xboole_0(A_54, B_55)) | k1_xboole_0=B_55 | k1_xboole_0=A_54)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.16/1.42  tff(c_256, plain, (![A_54, A_23]: (k1_setfam_1(k2_xboole_0(A_54, k1_tarski(A_23)))=k3_xboole_0(k1_setfam_1(A_54), A_23) | k1_tarski(A_23)=k1_xboole_0 | k1_xboole_0=A_54)), inference(superposition, [status(thm), theory('equality')], [c_24, c_236])).
% 2.16/1.42  tff(c_478, plain, (![A_65, A_66]: (k1_setfam_1(k2_xboole_0(A_65, k1_tarski(A_66)))=k3_xboole_0(k1_setfam_1(A_65), A_66) | k1_xboole_0=A_65)), inference(negUnitSimplification, [status(thm)], [c_65, c_256])).
% 2.16/1.42  tff(c_515, plain, (![A_5, B_6]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_5)), B_6)=k1_setfam_1(k2_tarski(A_5, B_6)) | k1_tarski(A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_478])).
% 2.16/1.42  tff(c_532, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6) | k1_tarski(A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_515])).
% 2.16/1.42  tff(c_533, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(negUnitSimplification, [status(thm)], [c_65, c_532])).
% 2.16/1.42  tff(c_26, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.16/1.42  tff(c_538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_533, c_26])).
% 2.16/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.42  
% 2.16/1.42  Inference rules
% 2.16/1.42  ----------------------
% 2.16/1.42  #Ref     : 0
% 2.16/1.42  #Sup     : 117
% 2.16/1.42  #Fact    : 0
% 2.16/1.42  #Define  : 0
% 2.16/1.42  #Split   : 0
% 2.16/1.42  #Chain   : 0
% 2.16/1.42  #Close   : 0
% 2.16/1.42  
% 2.16/1.42  Ordering : KBO
% 2.16/1.42  
% 2.16/1.42  Simplification rules
% 2.16/1.42  ----------------------
% 2.16/1.42  #Subsume      : 2
% 2.16/1.42  #Demod        : 64
% 2.16/1.42  #Tautology    : 75
% 2.16/1.42  #SimpNegUnit  : 15
% 2.16/1.42  #BackRed      : 1
% 2.16/1.42  
% 2.16/1.42  #Partial instantiations: 0
% 2.16/1.42  #Strategies tried      : 1
% 2.16/1.42  
% 2.16/1.42  Timing (in seconds)
% 2.16/1.42  ----------------------
% 2.16/1.43  Preprocessing        : 0.29
% 2.16/1.43  Parsing              : 0.15
% 2.16/1.43  CNF conversion       : 0.02
% 2.16/1.43  Main loop            : 0.26
% 2.16/1.43  Inferencing          : 0.11
% 2.16/1.43  Reduction            : 0.09
% 2.16/1.43  Demodulation         : 0.07
% 2.16/1.43  BG Simplification    : 0.02
% 2.16/1.43  Subsumption          : 0.04
% 2.16/1.43  Abstraction          : 0.02
% 2.16/1.43  MUC search           : 0.00
% 2.16/1.43  Cooper               : 0.00
% 2.16/1.43  Total                : 0.57
% 2.16/1.43  Index Insertion      : 0.00
% 2.16/1.43  Index Deletion       : 0.00
% 2.16/1.43  Index Matching       : 0.00
% 2.16/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
