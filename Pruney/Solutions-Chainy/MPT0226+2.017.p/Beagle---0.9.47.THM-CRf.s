%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:40 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   39 (  40 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   27 (  29 expanded)
%              Number of equality atoms :   26 (  28 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( k1_tarski(A) = k2_tarski(B,C)
     => B = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

tff(c_32,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ! [A_28,B_29] : k1_enumset1(A_28,A_28,B_29) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_360,plain,(
    ! [A_66,B_67,C_68] : k2_xboole_0(k2_tarski(A_66,B_67),k1_tarski(C_68)) = k1_enumset1(A_66,B_67,C_68) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_381,plain,(
    ! [A_27,C_68] : k2_xboole_0(k1_tarski(A_27),k1_tarski(C_68)) = k1_enumset1(A_27,A_27,C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_360])).

tff(c_385,plain,(
    ! [A_69,C_70] : k2_xboole_0(k1_tarski(A_69),k1_tarski(C_70)) = k2_tarski(A_69,C_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_381])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_150,plain,(
    ! [A_54,B_55] : k5_xboole_0(A_54,k4_xboole_0(B_55,A_54)) = k2_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_162,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_150])).

tff(c_165,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_162])).

tff(c_394,plain,(
    k2_tarski('#skF_2','#skF_1') = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_165])).

tff(c_30,plain,(
    ! [C_39,B_38,A_37] :
      ( C_39 = B_38
      | k2_tarski(B_38,C_39) != k1_tarski(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_434,plain,(
    ! [A_37] :
      ( '#skF_2' = '#skF_1'
      | k1_tarski(A_37) != k1_tarski('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_30])).

tff(c_438,plain,(
    ! [A_37] : k1_tarski(A_37) != k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_434])).

tff(c_443,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_438])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:28:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.29  
% 2.15/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.29  %$ k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.15/1.29  
% 2.15/1.29  %Foreground sorts:
% 2.15/1.29  
% 2.15/1.29  
% 2.15/1.29  %Background operators:
% 2.15/1.29  
% 2.15/1.29  
% 2.15/1.29  %Foreground operators:
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.15/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.15/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.15/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.15/1.29  
% 2.15/1.30  tff(f_62, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.15/1.30  tff(f_49, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.15/1.30  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.15/1.30  tff(f_45, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.15/1.30  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.15/1.30  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.15/1.30  tff(f_57, axiom, (![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (B = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 2.15/1.30  tff(c_32, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.15/1.30  tff(c_24, plain, (![A_28, B_29]: (k1_enumset1(A_28, A_28, B_29)=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.30  tff(c_22, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.15/1.30  tff(c_360, plain, (![A_66, B_67, C_68]: (k2_xboole_0(k2_tarski(A_66, B_67), k1_tarski(C_68))=k1_enumset1(A_66, B_67, C_68))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.15/1.30  tff(c_381, plain, (![A_27, C_68]: (k2_xboole_0(k1_tarski(A_27), k1_tarski(C_68))=k1_enumset1(A_27, A_27, C_68))), inference(superposition, [status(thm), theory('equality')], [c_22, c_360])).
% 2.15/1.30  tff(c_385, plain, (![A_69, C_70]: (k2_xboole_0(k1_tarski(A_69), k1_tarski(C_70))=k2_tarski(A_69, C_70))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_381])).
% 2.15/1.30  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.15/1.30  tff(c_34, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.15/1.30  tff(c_150, plain, (![A_54, B_55]: (k5_xboole_0(A_54, k4_xboole_0(B_55, A_54))=k2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.15/1.30  tff(c_162, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_150])).
% 2.15/1.30  tff(c_165, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_162])).
% 2.15/1.30  tff(c_394, plain, (k2_tarski('#skF_2', '#skF_1')=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_385, c_165])).
% 2.15/1.30  tff(c_30, plain, (![C_39, B_38, A_37]: (C_39=B_38 | k2_tarski(B_38, C_39)!=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.15/1.30  tff(c_434, plain, (![A_37]: ('#skF_2'='#skF_1' | k1_tarski(A_37)!=k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_394, c_30])).
% 2.15/1.30  tff(c_438, plain, (![A_37]: (k1_tarski(A_37)!=k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_434])).
% 2.15/1.30  tff(c_443, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_438])).
% 2.15/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.30  
% 2.15/1.30  Inference rules
% 2.15/1.30  ----------------------
% 2.15/1.30  #Ref     : 1
% 2.15/1.30  #Sup     : 104
% 2.15/1.30  #Fact    : 0
% 2.15/1.30  #Define  : 0
% 2.15/1.30  #Split   : 0
% 2.15/1.30  #Chain   : 0
% 2.15/1.30  #Close   : 0
% 2.15/1.30  
% 2.15/1.30  Ordering : KBO
% 2.15/1.30  
% 2.15/1.30  Simplification rules
% 2.15/1.30  ----------------------
% 2.15/1.30  #Subsume      : 0
% 2.15/1.30  #Demod        : 28
% 2.15/1.30  #Tautology    : 76
% 2.15/1.30  #SimpNegUnit  : 1
% 2.15/1.30  #BackRed      : 0
% 2.15/1.30  
% 2.15/1.30  #Partial instantiations: 0
% 2.15/1.30  #Strategies tried      : 1
% 2.15/1.30  
% 2.15/1.30  Timing (in seconds)
% 2.15/1.30  ----------------------
% 2.15/1.30  Preprocessing        : 0.28
% 2.15/1.30  Parsing              : 0.15
% 2.15/1.30  CNF conversion       : 0.02
% 2.15/1.30  Main loop            : 0.21
% 2.15/1.30  Inferencing          : 0.08
% 2.15/1.30  Reduction            : 0.08
% 2.15/1.30  Demodulation         : 0.06
% 2.15/1.30  BG Simplification    : 0.01
% 2.15/1.30  Subsumption          : 0.03
% 2.15/1.30  Abstraction          : 0.01
% 2.15/1.30  MUC search           : 0.00
% 2.15/1.30  Cooper               : 0.00
% 2.15/1.30  Total                : 0.51
% 2.15/1.30  Index Insertion      : 0.00
% 2.15/1.30  Index Deletion       : 0.00
% 2.15/1.30  Index Matching       : 0.00
% 2.15/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
