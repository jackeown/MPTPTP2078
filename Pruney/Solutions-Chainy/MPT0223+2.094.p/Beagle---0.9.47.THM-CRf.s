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
% DateTime   : Thu Dec  3 09:48:28 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   37 (  38 expanded)
%              Number of leaves         :   24 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :   21 (  23 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(c_26,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_77,plain,(
    ! [A_42,B_43] : k5_xboole_0(A_42,k3_xboole_0(A_42,B_43)) = k4_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_86,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) = k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_77])).

tff(c_89,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_86])).

tff(c_94,plain,(
    ! [A_44,B_45] : k5_xboole_0(A_44,k4_xboole_0(B_45,A_44)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_103,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_94])).

tff(c_106,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_103])).

tff(c_120,plain,(
    ! [B_49,A_50] :
      ( B_49 = A_50
      | k2_xboole_0(k1_tarski(A_50),k1_tarski(B_49)) != k1_tarski(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_123,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_120])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:34:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.19  
% 1.79/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.19  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.79/1.19  
% 1.79/1.19  %Foreground sorts:
% 1.79/1.19  
% 1.79/1.19  
% 1.79/1.19  %Background operators:
% 1.79/1.19  
% 1.79/1.19  
% 1.79/1.19  %Foreground operators:
% 1.79/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.79/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.79/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.79/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.79/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.79/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.79/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.79/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.79/1.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.79/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.79/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.79/1.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.79/1.19  
% 1.79/1.20  tff(f_56, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 1.79/1.20  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 1.79/1.20  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.79/1.20  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.79/1.20  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.79/1.20  tff(f_51, axiom, (![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 1.79/1.20  tff(c_26, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.79/1.20  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.79/1.20  tff(c_6, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.79/1.20  tff(c_28, plain, (k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.79/1.20  tff(c_77, plain, (![A_42, B_43]: (k5_xboole_0(A_42, k3_xboole_0(A_42, B_43))=k4_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.79/1.20  tff(c_86, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))=k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_77])).
% 1.79/1.20  tff(c_89, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_86])).
% 1.79/1.20  tff(c_94, plain, (![A_44, B_45]: (k5_xboole_0(A_44, k4_xboole_0(B_45, A_44))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.79/1.20  tff(c_103, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_89, c_94])).
% 1.79/1.20  tff(c_106, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_103])).
% 1.79/1.20  tff(c_120, plain, (![B_49, A_50]: (B_49=A_50 | k2_xboole_0(k1_tarski(A_50), k1_tarski(B_49))!=k1_tarski(A_50))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.79/1.20  tff(c_123, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_106, c_120])).
% 1.79/1.20  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_123])).
% 1.79/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.20  
% 1.79/1.20  Inference rules
% 1.79/1.20  ----------------------
% 1.79/1.20  #Ref     : 0
% 1.79/1.20  #Sup     : 25
% 1.79/1.20  #Fact    : 0
% 1.79/1.20  #Define  : 0
% 1.79/1.20  #Split   : 0
% 1.79/1.20  #Chain   : 0
% 1.79/1.20  #Close   : 0
% 1.79/1.20  
% 1.79/1.20  Ordering : KBO
% 1.79/1.20  
% 1.79/1.20  Simplification rules
% 1.79/1.20  ----------------------
% 1.79/1.20  #Subsume      : 0
% 1.79/1.20  #Demod        : 2
% 1.79/1.20  #Tautology    : 22
% 1.79/1.20  #SimpNegUnit  : 1
% 1.79/1.20  #BackRed      : 0
% 1.79/1.20  
% 1.79/1.20  #Partial instantiations: 0
% 1.79/1.20  #Strategies tried      : 1
% 1.79/1.20  
% 1.79/1.20  Timing (in seconds)
% 1.79/1.20  ----------------------
% 1.79/1.20  Preprocessing        : 0.30
% 1.79/1.20  Parsing              : 0.17
% 1.79/1.20  CNF conversion       : 0.02
% 1.79/1.20  Main loop            : 0.10
% 1.79/1.20  Inferencing          : 0.04
% 1.79/1.20  Reduction            : 0.03
% 1.79/1.20  Demodulation         : 0.02
% 1.79/1.20  BG Simplification    : 0.01
% 1.79/1.20  Subsumption          : 0.01
% 1.79/1.20  Abstraction          : 0.01
% 1.79/1.20  MUC search           : 0.00
% 1.79/1.20  Cooper               : 0.00
% 1.79/1.20  Total                : 0.42
% 1.79/1.20  Index Insertion      : 0.00
% 1.79/1.20  Index Deletion       : 0.00
% 1.79/1.20  Index Matching       : 0.00
% 1.79/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
