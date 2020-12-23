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
% DateTime   : Thu Dec  3 09:52:00 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   37 (  44 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  28 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_16,plain,(
    ! [A_23,B_24] : k2_enumset1(A_23,A_23,A_23,B_24) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_330,plain,(
    ! [A_61,B_62,C_63,D_64] : k2_xboole_0(k1_tarski(A_61),k1_enumset1(B_62,C_63,D_64)) = k2_enumset1(A_61,B_62,C_63,D_64) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [A_33,B_34] : k2_xboole_0(k1_tarski(A_33),B_34) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_353,plain,(
    ! [A_65,B_66,C_67,D_68] : k2_enumset1(A_65,B_66,C_67,D_68) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_24])).

tff(c_359,plain,(
    ! [A_23,B_24] : k2_tarski(A_23,B_24) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_353])).

tff(c_26,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_41,plain,(
    ! [A_38,B_39] : k3_xboole_0(A_38,k2_xboole_0(A_38,B_39)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) = k2_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_41])).

tff(c_53,plain,(
    ! [A_40,B_41] : k4_xboole_0(A_40,k2_xboole_0(A_40,B_41)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_60,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_53])).

tff(c_144,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k4_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_162,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) = k3_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_144])).

tff(c_169,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_60,c_162])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_359,c_169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:50:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.25  
% 2.13/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.26  %$ k5_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.13/1.26  
% 2.13/1.26  %Foreground sorts:
% 2.13/1.26  
% 2.13/1.26  
% 2.13/1.26  %Background operators:
% 2.13/1.26  
% 2.13/1.26  
% 2.13/1.26  %Foreground operators:
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.13/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.13/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.26  
% 2.13/1.27  tff(f_41, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 2.13/1.27  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 2.13/1.27  tff(f_50, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.13/1.27  tff(f_54, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.13/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.13/1.27  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.13/1.27  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.13/1.27  tff(c_16, plain, (![A_23, B_24]: (k2_enumset1(A_23, A_23, A_23, B_24)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.13/1.27  tff(c_330, plain, (![A_61, B_62, C_63, D_64]: (k2_xboole_0(k1_tarski(A_61), k1_enumset1(B_62, C_63, D_64))=k2_enumset1(A_61, B_62, C_63, D_64))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.27  tff(c_24, plain, (![A_33, B_34]: (k2_xboole_0(k1_tarski(A_33), B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.27  tff(c_353, plain, (![A_65, B_66, C_67, D_68]: (k2_enumset1(A_65, B_66, C_67, D_68)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_330, c_24])).
% 2.13/1.27  tff(c_359, plain, (![A_23, B_24]: (k2_tarski(A_23, B_24)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_353])).
% 2.13/1.27  tff(c_26, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.13/1.27  tff(c_41, plain, (![A_38, B_39]: (k3_xboole_0(A_38, k2_xboole_0(A_38, B_39))=A_38)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.13/1.27  tff(c_50, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)=k2_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26, c_41])).
% 2.13/1.27  tff(c_53, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k2_xboole_0(A_40, B_41))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.27  tff(c_60, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_26, c_53])).
% 2.13/1.27  tff(c_144, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k4_xboole_0(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.27  tff(c_162, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)=k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_60, c_144])).
% 2.13/1.27  tff(c_169, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_60, c_162])).
% 2.13/1.27  tff(c_361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_359, c_169])).
% 2.13/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.27  
% 2.13/1.27  Inference rules
% 2.13/1.27  ----------------------
% 2.13/1.27  #Ref     : 0
% 2.13/1.27  #Sup     : 93
% 2.13/1.27  #Fact    : 0
% 2.13/1.27  #Define  : 0
% 2.13/1.27  #Split   : 0
% 2.13/1.27  #Chain   : 0
% 2.13/1.27  #Close   : 0
% 2.13/1.27  
% 2.13/1.27  Ordering : KBO
% 2.13/1.27  
% 2.13/1.27  Simplification rules
% 2.13/1.27  ----------------------
% 2.13/1.27  #Subsume      : 2
% 2.13/1.27  #Demod        : 20
% 2.13/1.27  #Tautology    : 71
% 2.13/1.27  #SimpNegUnit  : 1
% 2.13/1.27  #BackRed      : 4
% 2.13/1.27  
% 2.13/1.27  #Partial instantiations: 0
% 2.13/1.27  #Strategies tried      : 1
% 2.13/1.27  
% 2.13/1.27  Timing (in seconds)
% 2.13/1.27  ----------------------
% 2.13/1.27  Preprocessing        : 0.31
% 2.13/1.27  Parsing              : 0.16
% 2.13/1.27  CNF conversion       : 0.02
% 2.13/1.27  Main loop            : 0.20
% 2.13/1.27  Inferencing          : 0.08
% 2.13/1.27  Reduction            : 0.07
% 2.13/1.27  Demodulation         : 0.06
% 2.13/1.27  BG Simplification    : 0.01
% 2.13/1.27  Subsumption          : 0.02
% 2.13/1.27  Abstraction          : 0.01
% 2.13/1.27  MUC search           : 0.00
% 2.13/1.27  Cooper               : 0.00
% 2.13/1.27  Total                : 0.53
% 2.13/1.27  Index Insertion      : 0.00
% 2.13/1.27  Index Deletion       : 0.00
% 2.13/1.27  Index Matching       : 0.00
% 2.13/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
