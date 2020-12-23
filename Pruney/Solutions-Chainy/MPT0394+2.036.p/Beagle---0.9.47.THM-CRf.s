%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:25 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   38 (  48 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  47 expanded)
%              Number of equality atoms :   29 (  38 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [A_36,B_37] :
      ( r1_xboole_0(A_36,B_37)
      | k3_xboole_0(A_36,B_37) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [B_20] : ~ r1_xboole_0(k1_tarski(B_20),k1_tarski(B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_96,plain,(
    ! [B_20] : k3_xboole_0(k1_tarski(B_20),k1_tarski(B_20)) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_90,c_24])).

tff(c_99,plain,(
    ! [B_20] : k1_tarski(B_20) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_96])).

tff(c_28,plain,(
    ! [A_23] : k1_setfam_1(k1_tarski(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [A_9,B_10] : k2_xboole_0(k1_tarski(A_9),k1_tarski(B_10)) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_295,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(k1_setfam_1(A_59),k1_setfam_1(B_60)) = k1_setfam_1(k2_xboole_0(A_59,B_60))
      | k1_xboole_0 = B_60
      | k1_xboole_0 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_318,plain,(
    ! [A_59,A_23] :
      ( k1_setfam_1(k2_xboole_0(A_59,k1_tarski(A_23))) = k3_xboole_0(k1_setfam_1(A_59),A_23)
      | k1_tarski(A_23) = k1_xboole_0
      | k1_xboole_0 = A_59 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_295])).

tff(c_476,plain,(
    ! [A_69,A_70] :
      ( k1_setfam_1(k2_xboole_0(A_69,k1_tarski(A_70))) = k3_xboole_0(k1_setfam_1(A_69),A_70)
      | k1_xboole_0 = A_69 ) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_318])).

tff(c_499,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_9)),B_10) = k1_setfam_1(k2_tarski(A_9,B_10))
      | k1_tarski(A_9) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_476])).

tff(c_510,plain,(
    ! [A_9,B_10] :
      ( k1_setfam_1(k2_tarski(A_9,B_10)) = k3_xboole_0(A_9,B_10)
      | k1_tarski(A_9) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_499])).

tff(c_511,plain,(
    ! [A_9,B_10] : k1_setfam_1(k2_tarski(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_510])).

tff(c_30,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_561,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:59:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.29  
% 2.06/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.29  %$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.06/1.29  
% 2.06/1.29  %Foreground sorts:
% 2.06/1.29  
% 2.06/1.29  
% 2.06/1.29  %Background operators:
% 2.06/1.29  
% 2.06/1.29  
% 2.06/1.29  %Foreground operators:
% 2.06/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.06/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.06/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.06/1.29  
% 2.06/1.30  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.06/1.30  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.06/1.30  tff(f_52, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.06/1.30  tff(f_64, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.06/1.30  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.06/1.30  tff(f_62, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.06/1.30  tff(f_67, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.06/1.30  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.30  tff(c_90, plain, (![A_36, B_37]: (r1_xboole_0(A_36, B_37) | k3_xboole_0(A_36, B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.30  tff(c_24, plain, (![B_20]: (~r1_xboole_0(k1_tarski(B_20), k1_tarski(B_20)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.06/1.30  tff(c_96, plain, (![B_20]: (k3_xboole_0(k1_tarski(B_20), k1_tarski(B_20))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_90, c_24])).
% 2.06/1.30  tff(c_99, plain, (![B_20]: (k1_tarski(B_20)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_96])).
% 2.06/1.30  tff(c_28, plain, (![A_23]: (k1_setfam_1(k1_tarski(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.06/1.30  tff(c_14, plain, (![A_9, B_10]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(B_10))=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.30  tff(c_295, plain, (![A_59, B_60]: (k3_xboole_0(k1_setfam_1(A_59), k1_setfam_1(B_60))=k1_setfam_1(k2_xboole_0(A_59, B_60)) | k1_xboole_0=B_60 | k1_xboole_0=A_59)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.06/1.30  tff(c_318, plain, (![A_59, A_23]: (k1_setfam_1(k2_xboole_0(A_59, k1_tarski(A_23)))=k3_xboole_0(k1_setfam_1(A_59), A_23) | k1_tarski(A_23)=k1_xboole_0 | k1_xboole_0=A_59)), inference(superposition, [status(thm), theory('equality')], [c_28, c_295])).
% 2.06/1.30  tff(c_476, plain, (![A_69, A_70]: (k1_setfam_1(k2_xboole_0(A_69, k1_tarski(A_70)))=k3_xboole_0(k1_setfam_1(A_69), A_70) | k1_xboole_0=A_69)), inference(negUnitSimplification, [status(thm)], [c_99, c_318])).
% 2.06/1.30  tff(c_499, plain, (![A_9, B_10]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_9)), B_10)=k1_setfam_1(k2_tarski(A_9, B_10)) | k1_tarski(A_9)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_476])).
% 2.06/1.30  tff(c_510, plain, (![A_9, B_10]: (k1_setfam_1(k2_tarski(A_9, B_10))=k3_xboole_0(A_9, B_10) | k1_tarski(A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_499])).
% 2.06/1.30  tff(c_511, plain, (![A_9, B_10]: (k1_setfam_1(k2_tarski(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(negUnitSimplification, [status(thm)], [c_99, c_510])).
% 2.06/1.30  tff(c_30, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.06/1.30  tff(c_561, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_511, c_30])).
% 2.06/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.30  
% 2.06/1.30  Inference rules
% 2.06/1.30  ----------------------
% 2.06/1.30  #Ref     : 0
% 2.06/1.30  #Sup     : 121
% 2.06/1.30  #Fact    : 0
% 2.06/1.30  #Define  : 0
% 2.06/1.30  #Split   : 0
% 2.06/1.30  #Chain   : 0
% 2.06/1.30  #Close   : 0
% 2.06/1.30  
% 2.06/1.30  Ordering : KBO
% 2.06/1.30  
% 2.06/1.30  Simplification rules
% 2.06/1.30  ----------------------
% 2.06/1.30  #Subsume      : 8
% 2.06/1.30  #Demod        : 62
% 2.06/1.30  #Tautology    : 78
% 2.06/1.30  #SimpNegUnit  : 8
% 2.06/1.30  #BackRed      : 3
% 2.06/1.30  
% 2.06/1.30  #Partial instantiations: 0
% 2.06/1.30  #Strategies tried      : 1
% 2.06/1.30  
% 2.06/1.30  Timing (in seconds)
% 2.06/1.30  ----------------------
% 2.06/1.30  Preprocessing        : 0.29
% 2.06/1.31  Parsing              : 0.16
% 2.06/1.31  CNF conversion       : 0.02
% 2.06/1.31  Main loop            : 0.24
% 2.06/1.31  Inferencing          : 0.10
% 2.06/1.31  Reduction            : 0.08
% 2.06/1.31  Demodulation         : 0.06
% 2.06/1.31  BG Simplification    : 0.02
% 2.06/1.31  Subsumption          : 0.04
% 2.06/1.31  Abstraction          : 0.02
% 2.06/1.31  MUC search           : 0.00
% 2.06/1.31  Cooper               : 0.00
% 2.06/1.31  Total                : 0.56
% 2.06/1.31  Index Insertion      : 0.00
% 2.06/1.31  Index Deletion       : 0.00
% 2.06/1.31  Index Matching       : 0.00
% 2.06/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
