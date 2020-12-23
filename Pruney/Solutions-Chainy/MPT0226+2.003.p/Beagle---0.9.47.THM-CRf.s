%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:38 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   41 (  42 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  33 expanded)
%              Number of equality atoms :   30 (  32 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( k1_tarski(A) = k2_tarski(B,C)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(c_40,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_30,plain,(
    ! [A_33,B_34] : k1_enumset1(A_33,A_33,B_34) = k2_tarski(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [A_32] : k2_tarski(A_32,A_32) = k1_tarski(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_516,plain,(
    ! [A_87,B_88,C_89] : k2_xboole_0(k2_tarski(A_87,B_88),k1_tarski(C_89)) = k1_enumset1(A_87,B_88,C_89) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_543,plain,(
    ! [A_32,C_89] : k2_xboole_0(k1_tarski(A_32),k1_tarski(C_89)) = k1_enumset1(A_32,A_32,C_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_516])).

tff(c_582,plain,(
    ! [A_92,C_93] : k2_xboole_0(k1_tarski(A_92),k1_tarski(C_93)) = k2_tarski(A_92,C_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_543])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_270,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k4_xboole_0(B_75,A_74)) = k2_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_288,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_270])).

tff(c_293,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_288])).

tff(c_591,plain,(
    k2_tarski('#skF_2','#skF_1') = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_582,c_293])).

tff(c_16,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_155,plain,(
    ! [B_55,A_56,C_57] :
      ( B_55 = A_56
      | k2_tarski(B_55,C_57) != k1_tarski(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_158,plain,(
    ! [A_56,A_12,B_13] :
      ( A_56 = A_12
      | k2_tarski(B_13,A_12) != k1_tarski(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_155])).

tff(c_643,plain,(
    ! [A_56] :
      ( A_56 = '#skF_1'
      | k1_tarski(A_56) != k1_tarski('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_158])).

tff(c_744,plain,(
    '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_643])).

tff(c_746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_744])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.38  
% 2.49/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.38  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.49/1.38  
% 2.49/1.38  %Foreground sorts:
% 2.49/1.38  
% 2.49/1.38  
% 2.49/1.38  %Background operators:
% 2.49/1.38  
% 2.49/1.38  
% 2.49/1.38  %Foreground operators:
% 2.49/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.49/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.49/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.49/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.49/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.49/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.49/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.49/1.38  
% 2.77/1.39  tff(f_70, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.77/1.39  tff(f_55, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.77/1.39  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.77/1.39  tff(f_47, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 2.77/1.39  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.77/1.39  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.77/1.39  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.77/1.39  tff(f_65, axiom, (![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_zfmisc_1)).
% 2.77/1.39  tff(c_40, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.77/1.39  tff(c_30, plain, (![A_33, B_34]: (k1_enumset1(A_33, A_33, B_34)=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.77/1.39  tff(c_28, plain, (![A_32]: (k2_tarski(A_32, A_32)=k1_tarski(A_32))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.77/1.39  tff(c_516, plain, (![A_87, B_88, C_89]: (k2_xboole_0(k2_tarski(A_87, B_88), k1_tarski(C_89))=k1_enumset1(A_87, B_88, C_89))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.77/1.39  tff(c_543, plain, (![A_32, C_89]: (k2_xboole_0(k1_tarski(A_32), k1_tarski(C_89))=k1_enumset1(A_32, A_32, C_89))), inference(superposition, [status(thm), theory('equality')], [c_28, c_516])).
% 2.77/1.39  tff(c_582, plain, (![A_92, C_93]: (k2_xboole_0(k1_tarski(A_92), k1_tarski(C_93))=k2_tarski(A_92, C_93))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_543])).
% 2.77/1.39  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.77/1.39  tff(c_42, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.77/1.39  tff(c_270, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k4_xboole_0(B_75, A_74))=k2_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.39  tff(c_288, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_270])).
% 2.77/1.39  tff(c_293, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_288])).
% 2.77/1.39  tff(c_591, plain, (k2_tarski('#skF_2', '#skF_1')=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_582, c_293])).
% 2.77/1.39  tff(c_16, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.77/1.39  tff(c_155, plain, (![B_55, A_56, C_57]: (B_55=A_56 | k2_tarski(B_55, C_57)!=k1_tarski(A_56))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.77/1.39  tff(c_158, plain, (![A_56, A_12, B_13]: (A_56=A_12 | k2_tarski(B_13, A_12)!=k1_tarski(A_56))), inference(superposition, [status(thm), theory('equality')], [c_16, c_155])).
% 2.77/1.39  tff(c_643, plain, (![A_56]: (A_56='#skF_1' | k1_tarski(A_56)!=k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_591, c_158])).
% 2.77/1.39  tff(c_744, plain, ('#skF_2'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_643])).
% 2.77/1.39  tff(c_746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_744])).
% 2.77/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.39  
% 2.77/1.39  Inference rules
% 2.77/1.39  ----------------------
% 2.77/1.39  #Ref     : 2
% 2.77/1.39  #Sup     : 181
% 2.77/1.39  #Fact    : 0
% 2.77/1.39  #Define  : 0
% 2.77/1.39  #Split   : 0
% 2.77/1.39  #Chain   : 0
% 2.77/1.39  #Close   : 0
% 2.77/1.39  
% 2.77/1.39  Ordering : KBO
% 2.77/1.39  
% 2.77/1.39  Simplification rules
% 2.77/1.39  ----------------------
% 2.77/1.39  #Subsume      : 6
% 2.77/1.39  #Demod        : 65
% 2.77/1.39  #Tautology    : 128
% 2.77/1.39  #SimpNegUnit  : 1
% 2.77/1.39  #BackRed      : 0
% 2.77/1.39  
% 2.77/1.39  #Partial instantiations: 0
% 2.77/1.39  #Strategies tried      : 1
% 2.77/1.39  
% 2.77/1.39  Timing (in seconds)
% 2.77/1.39  ----------------------
% 2.77/1.40  Preprocessing        : 0.32
% 2.77/1.40  Parsing              : 0.17
% 2.77/1.40  CNF conversion       : 0.02
% 2.77/1.40  Main loop            : 0.28
% 2.77/1.40  Inferencing          : 0.10
% 2.77/1.40  Reduction            : 0.10
% 2.77/1.40  Demodulation         : 0.08
% 2.77/1.40  BG Simplification    : 0.02
% 2.77/1.40  Subsumption          : 0.04
% 2.77/1.40  Abstraction          : 0.02
% 2.77/1.40  MUC search           : 0.00
% 2.77/1.40  Cooper               : 0.00
% 2.77/1.40  Total                : 0.62
% 2.77/1.40  Index Insertion      : 0.00
% 2.77/1.40  Index Deletion       : 0.00
% 2.77/1.40  Index Matching       : 0.00
% 2.77/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
