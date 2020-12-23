%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:43 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   44 (  87 expanded)
%              Number of leaves         :   20 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   35 (  87 expanded)
%              Number of equality atoms :   25 (  68 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => B = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_51,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_49,plain,(
    ! [B_38,A_39] : k2_tarski(B_38,A_39) = k2_tarski(A_39,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    k2_tarski('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_64,plain,(
    k2_tarski('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_30])).

tff(c_20,plain,(
    ! [A_27,B_28] : k1_enumset1(A_27,A_27,B_28) = k2_tarski(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_179,plain,(
    ! [A_49,B_50] : k2_enumset1(A_49,A_49,A_49,B_50) = k2_tarski(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ! [A_31] : k2_enumset1(A_31,A_31,A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_186,plain,(
    ! [B_50] : k2_tarski(B_50,B_50) = k1_tarski(B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_24])).

tff(c_653,plain,(
    ! [B_81,A_82,C_83] : k2_xboole_0(k2_tarski(B_81,A_82),k2_tarski(C_83,A_82)) = k1_enumset1(A_82,B_81,C_83) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1042,plain,(
    ! [B_97] : k2_xboole_0(k2_tarski(B_97,'#skF_3'),k1_tarski('#skF_1')) = k1_enumset1('#skF_3',B_97,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_653])).

tff(c_1082,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_1')) = k1_enumset1('#skF_3','#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_1042])).

tff(c_1102,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_1')) = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_20,c_1082])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1145,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1102,c_8])).

tff(c_26,plain,(
    ! [B_33,A_32] :
      ( B_33 = A_32
      | ~ r1_tarski(k1_tarski(A_32),k1_tarski(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1161,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1145,c_26])).

tff(c_28,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1170,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1161,c_28])).

tff(c_1169,plain,(
    k2_tarski('#skF_2','#skF_1') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1161,c_30])).

tff(c_1177,plain,(
    ! [B_99,A_100,C_101] : r1_tarski(k2_tarski(B_99,A_100),k1_enumset1(A_100,B_99,C_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_8])).

tff(c_1183,plain,(
    ! [B_50,C_101] : r1_tarski(k1_tarski(B_50),k1_enumset1(B_50,B_50,C_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_1177])).

tff(c_1251,plain,(
    ! [B_102,C_103] : r1_tarski(k1_tarski(B_102),k2_tarski(B_102,C_103)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1183])).

tff(c_1254,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1169,c_1251])).

tff(c_1334,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1254,c_26])).

tff(c_1338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1170,c_1334])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:24:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.55  
% 3.31/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.55  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.31/1.55  
% 3.31/1.55  %Foreground sorts:
% 3.31/1.55  
% 3.31/1.55  
% 3.31/1.55  %Background operators:
% 3.31/1.55  
% 3.31/1.55  
% 3.31/1.55  %Foreground operators:
% 3.31/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.31/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.31/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.31/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.31/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.31/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.31/1.55  
% 3.31/1.56  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.31/1.56  tff(f_60, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (B = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 3.31/1.56  tff(f_47, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.31/1.56  tff(f_49, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 3.31/1.56  tff(f_51, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 3.31/1.56  tff(f_45, axiom, (![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 3.31/1.56  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.31/1.56  tff(f_55, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 3.31/1.56  tff(c_49, plain, (![B_38, A_39]: (k2_tarski(B_38, A_39)=k2_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.31/1.56  tff(c_30, plain, (k2_tarski('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.31/1.56  tff(c_64, plain, (k2_tarski('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_49, c_30])).
% 3.31/1.56  tff(c_20, plain, (![A_27, B_28]: (k1_enumset1(A_27, A_27, B_28)=k2_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.31/1.56  tff(c_179, plain, (![A_49, B_50]: (k2_enumset1(A_49, A_49, A_49, B_50)=k2_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.31/1.56  tff(c_24, plain, (![A_31]: (k2_enumset1(A_31, A_31, A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.31/1.56  tff(c_186, plain, (![B_50]: (k2_tarski(B_50, B_50)=k1_tarski(B_50))), inference(superposition, [status(thm), theory('equality')], [c_179, c_24])).
% 3.31/1.56  tff(c_653, plain, (![B_81, A_82, C_83]: (k2_xboole_0(k2_tarski(B_81, A_82), k2_tarski(C_83, A_82))=k1_enumset1(A_82, B_81, C_83))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.31/1.56  tff(c_1042, plain, (![B_97]: (k2_xboole_0(k2_tarski(B_97, '#skF_3'), k1_tarski('#skF_1'))=k1_enumset1('#skF_3', B_97, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_653])).
% 3.31/1.56  tff(c_1082, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_1'))=k1_enumset1('#skF_3', '#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_186, c_1042])).
% 3.31/1.56  tff(c_1102, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_1'))=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_20, c_1082])).
% 3.31/1.56  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.31/1.56  tff(c_1145, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1102, c_8])).
% 3.31/1.56  tff(c_26, plain, (![B_33, A_32]: (B_33=A_32 | ~r1_tarski(k1_tarski(A_32), k1_tarski(B_33)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.31/1.56  tff(c_1161, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_1145, c_26])).
% 3.31/1.56  tff(c_28, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.31/1.56  tff(c_1170, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1161, c_28])).
% 3.31/1.56  tff(c_1169, plain, (k2_tarski('#skF_2', '#skF_1')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1161, c_30])).
% 3.31/1.56  tff(c_1177, plain, (![B_99, A_100, C_101]: (r1_tarski(k2_tarski(B_99, A_100), k1_enumset1(A_100, B_99, C_101)))), inference(superposition, [status(thm), theory('equality')], [c_653, c_8])).
% 3.31/1.56  tff(c_1183, plain, (![B_50, C_101]: (r1_tarski(k1_tarski(B_50), k1_enumset1(B_50, B_50, C_101)))), inference(superposition, [status(thm), theory('equality')], [c_186, c_1177])).
% 3.31/1.56  tff(c_1251, plain, (![B_102, C_103]: (r1_tarski(k1_tarski(B_102), k2_tarski(B_102, C_103)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1183])).
% 3.31/1.56  tff(c_1254, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1169, c_1251])).
% 3.31/1.56  tff(c_1334, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_1254, c_26])).
% 3.31/1.56  tff(c_1338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1170, c_1334])).
% 3.31/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.56  
% 3.31/1.56  Inference rules
% 3.31/1.56  ----------------------
% 3.31/1.56  #Ref     : 0
% 3.31/1.56  #Sup     : 337
% 3.31/1.56  #Fact    : 0
% 3.31/1.56  #Define  : 0
% 3.31/1.56  #Split   : 0
% 3.31/1.56  #Chain   : 0
% 3.31/1.56  #Close   : 0
% 3.31/1.56  
% 3.31/1.56  Ordering : KBO
% 3.31/1.56  
% 3.31/1.56  Simplification rules
% 3.31/1.56  ----------------------
% 3.31/1.56  #Subsume      : 11
% 3.31/1.56  #Demod        : 152
% 3.31/1.56  #Tautology    : 169
% 3.31/1.56  #SimpNegUnit  : 1
% 3.31/1.56  #BackRed      : 9
% 3.31/1.56  
% 3.31/1.56  #Partial instantiations: 0
% 3.31/1.56  #Strategies tried      : 1
% 3.31/1.56  
% 3.31/1.56  Timing (in seconds)
% 3.31/1.56  ----------------------
% 3.31/1.56  Preprocessing        : 0.33
% 3.31/1.56  Parsing              : 0.18
% 3.31/1.56  CNF conversion       : 0.02
% 3.31/1.56  Main loop            : 0.42
% 3.31/1.56  Inferencing          : 0.14
% 3.31/1.56  Reduction            : 0.17
% 3.31/1.56  Demodulation         : 0.14
% 3.31/1.56  BG Simplification    : 0.02
% 3.31/1.56  Subsumption          : 0.07
% 3.31/1.56  Abstraction          : 0.02
% 3.31/1.56  MUC search           : 0.00
% 3.31/1.56  Cooper               : 0.00
% 3.31/1.57  Total                : 0.77
% 3.31/1.57  Index Insertion      : 0.00
% 3.31/1.57  Index Deletion       : 0.00
% 3.31/1.57  Index Matching       : 0.00
% 3.31/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
