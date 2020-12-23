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
% DateTime   : Thu Dec  3 09:48:38 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   38 (  39 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   27 (  29 expanded)
%              Number of equality atoms :   26 (  28 expanded)
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

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( k1_tarski(A) = k2_tarski(B,C)
     => B = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_zfmisc_1)).

tff(c_42,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [A_35] : k2_tarski(A_35,A_35) = k1_tarski(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_558,plain,(
    ! [A_88,B_89,C_90] : k2_xboole_0(k2_tarski(A_88,B_89),k1_tarski(C_90)) = k1_enumset1(A_88,B_89,C_90) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_585,plain,(
    ! [A_35,C_90] : k2_xboole_0(k1_tarski(A_35),k1_tarski(C_90)) = k1_enumset1(A_35,A_35,C_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_558])).

tff(c_589,plain,(
    ! [A_91,C_92] : k2_xboole_0(k1_tarski(A_91),k1_tarski(C_92)) = k2_tarski(A_91,C_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_585])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_244,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k4_xboole_0(B_72,A_71)) = k2_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_262,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_244])).

tff(c_267,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_262])).

tff(c_602,plain,(
    k2_tarski('#skF_2','#skF_1') = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_267])).

tff(c_40,plain,(
    ! [C_49,B_48,A_47] :
      ( C_49 = B_48
      | k2_tarski(B_48,C_49) != k1_tarski(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_650,plain,(
    ! [A_47] :
      ( '#skF_2' = '#skF_1'
      | k1_tarski(A_47) != k1_tarski('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_40])).

tff(c_670,plain,(
    ! [A_47] : k1_tarski(A_47) != k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_650])).

tff(c_675,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_670])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 10:07:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.38  
% 2.48/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.38  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.48/1.38  
% 2.48/1.38  %Foreground sorts:
% 2.48/1.38  
% 2.48/1.38  
% 2.48/1.38  %Background operators:
% 2.48/1.38  
% 2.48/1.38  
% 2.48/1.38  %Foreground operators:
% 2.48/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.48/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.48/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.48/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.48/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.48/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.48/1.38  
% 2.48/1.39  tff(f_72, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.48/1.39  tff(f_57, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.48/1.39  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.48/1.39  tff(f_49, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 2.48/1.39  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.48/1.39  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.48/1.39  tff(f_67, axiom, (![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (B = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 2.48/1.39  tff(c_42, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.48/1.39  tff(c_32, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.48/1.39  tff(c_30, plain, (![A_35]: (k2_tarski(A_35, A_35)=k1_tarski(A_35))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.48/1.39  tff(c_558, plain, (![A_88, B_89, C_90]: (k2_xboole_0(k2_tarski(A_88, B_89), k1_tarski(C_90))=k1_enumset1(A_88, B_89, C_90))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.48/1.39  tff(c_585, plain, (![A_35, C_90]: (k2_xboole_0(k1_tarski(A_35), k1_tarski(C_90))=k1_enumset1(A_35, A_35, C_90))), inference(superposition, [status(thm), theory('equality')], [c_30, c_558])).
% 2.48/1.39  tff(c_589, plain, (![A_91, C_92]: (k2_xboole_0(k1_tarski(A_91), k1_tarski(C_92))=k2_tarski(A_91, C_92))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_585])).
% 2.48/1.39  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.48/1.39  tff(c_44, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.48/1.39  tff(c_244, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k4_xboole_0(B_72, A_71))=k2_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.48/1.39  tff(c_262, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_244])).
% 2.48/1.39  tff(c_267, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_262])).
% 2.48/1.39  tff(c_602, plain, (k2_tarski('#skF_2', '#skF_1')=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_589, c_267])).
% 2.48/1.39  tff(c_40, plain, (![C_49, B_48, A_47]: (C_49=B_48 | k2_tarski(B_48, C_49)!=k1_tarski(A_47))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.48/1.39  tff(c_650, plain, (![A_47]: ('#skF_2'='#skF_1' | k1_tarski(A_47)!=k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_602, c_40])).
% 2.48/1.39  tff(c_670, plain, (![A_47]: (k1_tarski(A_47)!=k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_650])).
% 2.48/1.39  tff(c_675, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_670])).
% 2.48/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.39  
% 2.48/1.39  Inference rules
% 2.48/1.39  ----------------------
% 2.48/1.39  #Ref     : 1
% 2.48/1.39  #Sup     : 161
% 2.48/1.39  #Fact    : 0
% 2.48/1.39  #Define  : 0
% 2.48/1.39  #Split   : 0
% 2.48/1.39  #Chain   : 0
% 2.48/1.39  #Close   : 0
% 2.48/1.39  
% 2.48/1.39  Ordering : KBO
% 2.48/1.39  
% 2.48/1.39  Simplification rules
% 2.48/1.39  ----------------------
% 2.48/1.39  #Subsume      : 2
% 2.48/1.39  #Demod        : 56
% 2.48/1.39  #Tautology    : 119
% 2.48/1.39  #SimpNegUnit  : 1
% 2.48/1.39  #BackRed      : 0
% 2.48/1.39  
% 2.48/1.39  #Partial instantiations: 0
% 2.48/1.39  #Strategies tried      : 1
% 2.48/1.39  
% 2.48/1.39  Timing (in seconds)
% 2.48/1.39  ----------------------
% 2.48/1.39  Preprocessing        : 0.29
% 2.48/1.39  Parsing              : 0.16
% 2.48/1.39  CNF conversion       : 0.02
% 2.48/1.39  Main loop            : 0.26
% 2.48/1.39  Inferencing          : 0.09
% 2.48/1.39  Reduction            : 0.10
% 2.48/1.39  Demodulation         : 0.08
% 2.48/1.39  BG Simplification    : 0.02
% 2.48/1.39  Subsumption          : 0.04
% 2.48/1.39  Abstraction          : 0.01
% 2.48/1.39  MUC search           : 0.00
% 2.48/1.39  Cooper               : 0.00
% 2.48/1.39  Total                : 0.58
% 2.48/1.39  Index Insertion      : 0.00
% 2.48/1.39  Index Deletion       : 0.00
% 2.48/1.39  Index Matching       : 0.00
% 2.48/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
