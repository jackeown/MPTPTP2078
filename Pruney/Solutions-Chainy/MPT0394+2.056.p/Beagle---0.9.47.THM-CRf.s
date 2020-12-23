%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:28 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   35 (  46 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   30 (  41 expanded)
%              Number of equality atoms :   29 (  40 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ! [A_22,B_23] : k2_xboole_0(k1_tarski(A_22),k1_tarski(B_23)) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),B_12) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_58,plain,(
    ! [A_24,B_25] : k2_tarski(A_24,B_25) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_12])).

tff(c_60,plain,(
    ! [A_5] : k1_tarski(A_5) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_58])).

tff(c_16,plain,(
    ! [A_15] : k1_setfam_1(k1_tarski(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k1_tarski(A_3),k1_tarski(B_4)) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_132,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(k1_setfam_1(A_36),k1_setfam_1(B_37)) = k1_setfam_1(k2_xboole_0(A_36,B_37))
      | k1_xboole_0 = B_37
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_144,plain,(
    ! [A_15,B_37] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_15),B_37)) = k3_xboole_0(A_15,k1_setfam_1(B_37))
      | k1_xboole_0 = B_37
      | k1_tarski(A_15) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_132])).

tff(c_152,plain,(
    ! [A_38,B_39] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_38),B_39)) = k3_xboole_0(A_38,k1_setfam_1(B_39))
      | k1_xboole_0 = B_39 ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_144])).

tff(c_167,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,k1_setfam_1(k1_tarski(B_4))) = k1_setfam_1(k2_tarski(A_3,B_4))
      | k1_tarski(B_4) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_152])).

tff(c_172,plain,(
    ! [A_3,B_4] :
      ( k1_setfam_1(k2_tarski(A_3,B_4)) = k3_xboole_0(A_3,B_4)
      | k1_tarski(B_4) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_167])).

tff(c_173,plain,(
    ! [A_3,B_4] : k1_setfam_1(k2_tarski(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_172])).

tff(c_18,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:49:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.20  
% 1.84/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.20  %$ k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.84/1.20  
% 1.84/1.20  %Foreground sorts:
% 1.84/1.20  
% 1.84/1.20  
% 1.84/1.20  %Background operators:
% 1.84/1.20  
% 1.84/1.20  
% 1.84/1.20  %Foreground operators:
% 1.84/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.84/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.84/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.84/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.84/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.84/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.84/1.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.84/1.20  
% 1.92/1.21  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.92/1.21  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.92/1.21  tff(f_38, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.92/1.21  tff(f_50, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 1.92/1.21  tff(f_48, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 1.92/1.21  tff(f_53, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.92/1.21  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.21  tff(c_47, plain, (![A_22, B_23]: (k2_xboole_0(k1_tarski(A_22), k1_tarski(B_23))=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.21  tff(c_12, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.92/1.21  tff(c_58, plain, (![A_24, B_25]: (k2_tarski(A_24, B_25)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_47, c_12])).
% 1.92/1.21  tff(c_60, plain, (![A_5]: (k1_tarski(A_5)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_58])).
% 1.92/1.21  tff(c_16, plain, (![A_15]: (k1_setfam_1(k1_tarski(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.92/1.21  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k1_tarski(A_3), k1_tarski(B_4))=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.21  tff(c_132, plain, (![A_36, B_37]: (k3_xboole_0(k1_setfam_1(A_36), k1_setfam_1(B_37))=k1_setfam_1(k2_xboole_0(A_36, B_37)) | k1_xboole_0=B_37 | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.92/1.21  tff(c_144, plain, (![A_15, B_37]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_15), B_37))=k3_xboole_0(A_15, k1_setfam_1(B_37)) | k1_xboole_0=B_37 | k1_tarski(A_15)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_132])).
% 1.92/1.21  tff(c_152, plain, (![A_38, B_39]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_38), B_39))=k3_xboole_0(A_38, k1_setfam_1(B_39)) | k1_xboole_0=B_39)), inference(negUnitSimplification, [status(thm)], [c_60, c_144])).
% 1.92/1.21  tff(c_167, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k1_setfam_1(k1_tarski(B_4)))=k1_setfam_1(k2_tarski(A_3, B_4)) | k1_tarski(B_4)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_152])).
% 1.92/1.21  tff(c_172, plain, (![A_3, B_4]: (k1_setfam_1(k2_tarski(A_3, B_4))=k3_xboole_0(A_3, B_4) | k1_tarski(B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_167])).
% 1.92/1.21  tff(c_173, plain, (![A_3, B_4]: (k1_setfam_1(k2_tarski(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(negUnitSimplification, [status(thm)], [c_60, c_172])).
% 1.92/1.21  tff(c_18, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.92/1.21  tff(c_208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_18])).
% 1.92/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.21  
% 1.92/1.21  Inference rules
% 1.92/1.21  ----------------------
% 1.92/1.21  #Ref     : 0
% 1.92/1.21  #Sup     : 45
% 1.92/1.21  #Fact    : 0
% 1.92/1.21  #Define  : 0
% 1.92/1.21  #Split   : 0
% 1.92/1.21  #Chain   : 0
% 1.92/1.21  #Close   : 0
% 1.92/1.21  
% 1.92/1.21  Ordering : KBO
% 1.92/1.21  
% 1.92/1.21  Simplification rules
% 1.92/1.21  ----------------------
% 1.92/1.21  #Subsume      : 0
% 1.92/1.21  #Demod        : 10
% 1.92/1.21  #Tautology    : 27
% 1.92/1.21  #SimpNegUnit  : 8
% 1.92/1.21  #BackRed      : 1
% 1.92/1.21  
% 1.92/1.21  #Partial instantiations: 0
% 1.92/1.21  #Strategies tried      : 1
% 1.92/1.21  
% 1.92/1.21  Timing (in seconds)
% 1.92/1.21  ----------------------
% 1.92/1.21  Preprocessing        : 0.27
% 1.92/1.21  Parsing              : 0.14
% 1.92/1.21  CNF conversion       : 0.02
% 1.92/1.21  Main loop            : 0.15
% 1.92/1.21  Inferencing          : 0.06
% 1.92/1.21  Reduction            : 0.05
% 1.92/1.21  Demodulation         : 0.04
% 1.92/1.21  BG Simplification    : 0.01
% 1.92/1.21  Subsumption          : 0.02
% 1.92/1.21  Abstraction          : 0.01
% 1.92/1.21  MUC search           : 0.00
% 1.92/1.21  Cooper               : 0.00
% 1.92/1.21  Total                : 0.44
% 1.92/1.21  Index Insertion      : 0.00
% 1.92/1.21  Index Deletion       : 0.00
% 1.92/1.21  Index Matching       : 0.00
% 1.92/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
