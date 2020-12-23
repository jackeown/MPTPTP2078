%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:43 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 175 expanded)
%              Number of leaves         :   22 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :   35 ( 162 expanded)
%              Number of equality atoms :   34 ( 161 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_40,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_47,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_20,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_6])).

tff(c_128,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_4])).

tff(c_151,plain,(
    ! [A_25,B_26] : k3_tarski(k2_tarski(A_25,B_26)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_160,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k3_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_151])).

tff(c_172,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_160])).

tff(c_185,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_6])).

tff(c_188,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_185])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_43,plain,(
    ! [A_16,B_17] : k2_xboole_0(k1_tarski(A_16),B_17) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_47,plain,(
    ! [A_16] : k1_tarski(A_16) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_43])).

tff(c_195,plain,(
    ! [A_16] : k1_tarski(A_16) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_47])).

tff(c_197,plain,(
    ! [A_1] : k2_xboole_0(A_1,'#skF_1') = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_2])).

tff(c_199,plain,(
    k3_tarski('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_188,c_16])).

tff(c_192,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_128])).

tff(c_8,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_320,plain,(
    ! [A_40,B_41] : k3_tarski(k2_tarski(A_40,B_41)) = k2_xboole_0(B_41,A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_151])).

tff(c_332,plain,(
    k2_xboole_0('#skF_2','#skF_1') = k3_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_320])).

tff(c_347,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_199,c_332])).

tff(c_350,plain,(
    k2_tarski('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_192])).

tff(c_10,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_366,plain,(
    k1_tarski('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_10])).

tff(c_375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_366])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.30  
% 1.88/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.30  %$ k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.09/1.30  
% 2.09/1.30  %Foreground sorts:
% 2.09/1.30  
% 2.09/1.30  
% 2.09/1.30  %Background operators:
% 2.09/1.30  
% 2.09/1.30  
% 2.09/1.30  %Foreground operators:
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.30  
% 2.09/1.31  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.09/1.31  tff(f_40, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.09/1.31  tff(f_47, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.09/1.31  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.09/1.31  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.09/1.31  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.09/1.31  tff(f_43, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.09/1.31  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.09/1.31  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.09/1.31  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.09/1.31  tff(c_16, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.09/1.31  tff(c_20, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.09/1.31  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.31  tff(c_121, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_20, c_6])).
% 2.09/1.31  tff(c_128, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_121, c_4])).
% 2.09/1.31  tff(c_151, plain, (![A_25, B_26]: (k3_tarski(k2_tarski(A_25, B_26))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.31  tff(c_160, plain, (k2_xboole_0('#skF_1', '#skF_2')=k3_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_128, c_151])).
% 2.09/1.31  tff(c_172, plain, (k2_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_160])).
% 2.09/1.31  tff(c_185, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_172, c_6])).
% 2.09/1.31  tff(c_188, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_185])).
% 2.09/1.31  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.09/1.31  tff(c_43, plain, (![A_16, B_17]: (k2_xboole_0(k1_tarski(A_16), B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.09/1.31  tff(c_47, plain, (![A_16]: (k1_tarski(A_16)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_43])).
% 2.09/1.31  tff(c_195, plain, (![A_16]: (k1_tarski(A_16)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_47])).
% 2.09/1.31  tff(c_197, plain, (![A_1]: (k2_xboole_0(A_1, '#skF_1')=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_188, c_2])).
% 2.09/1.31  tff(c_199, plain, (k3_tarski('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_188, c_188, c_16])).
% 2.09/1.31  tff(c_192, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_188, c_128])).
% 2.09/1.31  tff(c_8, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.09/1.31  tff(c_320, plain, (![A_40, B_41]: (k3_tarski(k2_tarski(A_40, B_41))=k2_xboole_0(B_41, A_40))), inference(superposition, [status(thm), theory('equality')], [c_8, c_151])).
% 2.09/1.31  tff(c_332, plain, (k2_xboole_0('#skF_2', '#skF_1')=k3_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_192, c_320])).
% 2.09/1.31  tff(c_347, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_197, c_199, c_332])).
% 2.09/1.31  tff(c_350, plain, (k2_tarski('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_347, c_192])).
% 2.09/1.31  tff(c_10, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.09/1.31  tff(c_366, plain, (k1_tarski('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_350, c_10])).
% 2.09/1.31  tff(c_375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_195, c_366])).
% 2.09/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.31  
% 2.09/1.31  Inference rules
% 2.09/1.31  ----------------------
% 2.09/1.31  #Ref     : 0
% 2.09/1.31  #Sup     : 97
% 2.09/1.31  #Fact    : 0
% 2.09/1.31  #Define  : 0
% 2.09/1.31  #Split   : 0
% 2.09/1.31  #Chain   : 0
% 2.09/1.31  #Close   : 0
% 2.09/1.31  
% 2.09/1.31  Ordering : KBO
% 2.09/1.31  
% 2.09/1.31  Simplification rules
% 2.09/1.31  ----------------------
% 2.09/1.31  #Subsume      : 2
% 2.09/1.31  #Demod        : 36
% 2.09/1.31  #Tautology    : 80
% 2.09/1.31  #SimpNegUnit  : 1
% 2.09/1.31  #BackRed      : 14
% 2.09/1.31  
% 2.09/1.31  #Partial instantiations: 0
% 2.09/1.31  #Strategies tried      : 1
% 2.09/1.31  
% 2.09/1.31  Timing (in seconds)
% 2.09/1.31  ----------------------
% 2.09/1.32  Preprocessing        : 0.30
% 2.09/1.32  Parsing              : 0.15
% 2.09/1.32  CNF conversion       : 0.02
% 2.09/1.32  Main loop            : 0.19
% 2.09/1.32  Inferencing          : 0.07
% 2.09/1.32  Reduction            : 0.07
% 2.09/1.32  Demodulation         : 0.05
% 2.09/1.32  BG Simplification    : 0.01
% 2.09/1.32  Subsumption          : 0.03
% 2.09/1.32  Abstraction          : 0.01
% 2.09/1.32  MUC search           : 0.00
% 2.09/1.32  Cooper               : 0.00
% 2.09/1.32  Total                : 0.52
% 2.09/1.32  Index Insertion      : 0.00
% 2.09/1.32  Index Deletion       : 0.00
% 2.09/1.32  Index Matching       : 0.00
% 2.09/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
