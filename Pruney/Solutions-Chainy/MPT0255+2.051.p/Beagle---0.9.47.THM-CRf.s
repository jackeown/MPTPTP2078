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
% DateTime   : Thu Dec  3 09:51:46 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 106 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   34 ( 108 expanded)
%              Number of equality atoms :   26 (  72 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_20,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_590,plain,(
    ! [A_60,B_61,C_62] : k2_xboole_0(k1_tarski(A_60),k2_tarski(B_61,C_62)) = k1_enumset1(A_60,B_61,C_62) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_155,plain,(
    ! [A_38,B_39] :
      ( k2_xboole_0(A_38,B_39) = B_39
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_230,plain,(
    ! [A_42] : k2_xboole_0(k1_xboole_0,A_42) = A_42 ),
    inference(resolution,[status(thm)],[c_12,c_155])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_247,plain,(
    ! [A_42] : k2_xboole_0(A_42,k1_xboole_0) = A_42 ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_2])).

tff(c_275,plain,(
    ! [A_43] : k2_xboole_0(A_43,k1_xboole_0) = A_43 ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_2])).

tff(c_28,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_14])).

tff(c_176,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_155])).

tff(c_289,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_176])).

tff(c_50,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_28])).

tff(c_365,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_68])).

tff(c_369,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_365])).

tff(c_26,plain,(
    ! [A_21,B_22] : k2_xboole_0(k1_tarski(A_21),B_22) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_385,plain,(
    ! [A_21,B_22] : k2_xboole_0(k1_tarski(A_21),B_22) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_26])).

tff(c_648,plain,(
    ! [A_64,B_65,C_66] : k1_enumset1(A_64,B_65,C_66) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_590,c_385])).

tff(c_650,plain,(
    ! [A_14,B_15] : k2_tarski(A_14,B_15) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_648])).

tff(c_319,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_275])).

tff(c_457,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_319])).

tff(c_652,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_650,c_457])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:39:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.28  
% 2.07/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.29  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
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
% 2.07/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.07/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.29  
% 2.07/1.29  tff(f_47, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.07/1.29  tff(f_43, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.07/1.29  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.07/1.29  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.07/1.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.07/1.29  tff(f_58, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.07/1.29  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.07/1.29  tff(f_54, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.07/1.29  tff(c_20, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.07/1.29  tff(c_590, plain, (![A_60, B_61, C_62]: (k2_xboole_0(k1_tarski(A_60), k2_tarski(B_61, C_62))=k1_enumset1(A_60, B_61, C_62))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.07/1.29  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.07/1.29  tff(c_155, plain, (![A_38, B_39]: (k2_xboole_0(A_38, B_39)=B_39 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.07/1.29  tff(c_230, plain, (![A_42]: (k2_xboole_0(k1_xboole_0, A_42)=A_42)), inference(resolution, [status(thm)], [c_12, c_155])).
% 2.07/1.29  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.29  tff(c_247, plain, (![A_42]: (k2_xboole_0(A_42, k1_xboole_0)=A_42)), inference(superposition, [status(thm), theory('equality')], [c_230, c_2])).
% 2.07/1.29  tff(c_275, plain, (![A_43]: (k2_xboole_0(A_43, k1_xboole_0)=A_43)), inference(superposition, [status(thm), theory('equality')], [c_230, c_2])).
% 2.07/1.29  tff(c_28, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.07/1.29  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.07/1.29  tff(c_46, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_14])).
% 2.07/1.29  tff(c_176, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_155])).
% 2.07/1.29  tff(c_289, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_275, c_176])).
% 2.07/1.29  tff(c_50, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.29  tff(c_68, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_50, c_28])).
% 2.07/1.29  tff(c_365, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_289, c_68])).
% 2.07/1.29  tff(c_369, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_247, c_365])).
% 2.07/1.29  tff(c_26, plain, (![A_21, B_22]: (k2_xboole_0(k1_tarski(A_21), B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.07/1.29  tff(c_385, plain, (![A_21, B_22]: (k2_xboole_0(k1_tarski(A_21), B_22)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_369, c_26])).
% 2.07/1.29  tff(c_648, plain, (![A_64, B_65, C_66]: (k1_enumset1(A_64, B_65, C_66)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_590, c_385])).
% 2.07/1.29  tff(c_650, plain, (![A_14, B_15]: (k2_tarski(A_14, B_15)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_648])).
% 2.07/1.29  tff(c_319, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_176, c_275])).
% 2.07/1.29  tff(c_457, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_369, c_319])).
% 2.07/1.29  tff(c_652, plain, $false, inference(negUnitSimplification, [status(thm)], [c_650, c_457])).
% 2.07/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.29  
% 2.07/1.29  Inference rules
% 2.07/1.29  ----------------------
% 2.07/1.29  #Ref     : 0
% 2.07/1.30  #Sup     : 150
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
% 2.07/1.30  #Subsume      : 14
% 2.07/1.30  #Demod        : 78
% 2.07/1.30  #Tautology    : 106
% 2.07/1.30  #SimpNegUnit  : 1
% 2.07/1.30  #BackRed      : 13
% 2.07/1.30  
% 2.07/1.30  #Partial instantiations: 0
% 2.07/1.30  #Strategies tried      : 1
% 2.07/1.30  
% 2.07/1.30  Timing (in seconds)
% 2.07/1.30  ----------------------
% 2.07/1.30  Preprocessing        : 0.28
% 2.07/1.30  Parsing              : 0.15
% 2.07/1.30  CNF conversion       : 0.01
% 2.07/1.30  Main loop            : 0.24
% 2.07/1.30  Inferencing          : 0.08
% 2.07/1.30  Reduction            : 0.09
% 2.07/1.30  Demodulation         : 0.07
% 2.07/1.30  BG Simplification    : 0.01
% 2.07/1.30  Subsumption          : 0.04
% 2.07/1.30  Abstraction          : 0.01
% 2.07/1.30  MUC search           : 0.00
% 2.07/1.30  Cooper               : 0.00
% 2.07/1.30  Total                : 0.54
% 2.07/1.30  Index Insertion      : 0.00
% 2.07/1.30  Index Deletion       : 0.00
% 2.07/1.30  Index Matching       : 0.00
% 2.07/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
