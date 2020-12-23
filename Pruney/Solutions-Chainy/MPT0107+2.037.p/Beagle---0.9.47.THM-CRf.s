%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:57 EST 2020

% Result     : Theorem 5.79s
% Output     : CNFRefutation 5.79s
% Verified   : 
% Statistics : Number of formulae       :   39 (  56 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :   29 (  46 expanded)
%              Number of equality atoms :   28 (  45 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_280,plain,(
    ! [A_38,B_39] : k4_xboole_0(k2_xboole_0(A_38,B_39),B_39) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_293,plain,(
    ! [A_38] : k4_xboole_0(A_38,k1_xboole_0) = k2_xboole_0(A_38,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_8])).

tff(c_309,plain,(
    ! [A_38] : k2_xboole_0(A_38,k1_xboole_0) = A_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_293])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_171,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_189,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_171])).

tff(c_192,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_189])).

tff(c_595,plain,(
    ! [A_49,B_50,C_51] : k3_xboole_0(k4_xboole_0(A_49,B_50),k4_xboole_0(A_49,C_51)) = k4_xboole_0(A_49,k2_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_657,plain,(
    ! [A_6,B_50] : k4_xboole_0(A_6,k2_xboole_0(B_50,k1_xboole_0)) = k3_xboole_0(k4_xboole_0(A_6,B_50),A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_595])).

tff(c_1083,plain,(
    ! [A_66,B_67] : k3_xboole_0(k4_xboole_0(A_66,B_67),A_66) = k4_xboole_0(A_66,B_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_657])).

tff(c_1095,plain,(
    ! [A_66,B_67] : k4_xboole_0(k4_xboole_0(A_66,B_67),k4_xboole_0(A_66,B_67)) = k4_xboole_0(k4_xboole_0(A_66,B_67),A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_1083,c_12])).

tff(c_1150,plain,(
    ! [A_68,B_69] : k4_xboole_0(k4_xboole_0(A_68,B_69),A_68) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_1095])).

tff(c_1320,plain,(
    ! [A_72,B_73] : k4_xboole_0(k3_xboole_0(A_72,B_73),A_72) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1150])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1346,plain,(
    ! [A_72,B_73] : k2_xboole_0(k4_xboole_0(A_72,k3_xboole_0(A_72,B_73)),k1_xboole_0) = k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1320,c_4])).

tff(c_1405,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k4_xboole_0(A_72,B_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_12,c_1346])).

tff(c_24,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_9587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1405,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:54:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.79/2.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.79/2.21  
% 5.79/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.79/2.21  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 5.79/2.21  
% 5.79/2.21  %Foreground sorts:
% 5.79/2.21  
% 5.79/2.21  
% 5.79/2.21  %Background operators:
% 5.79/2.21  
% 5.79/2.21  
% 5.79/2.21  %Foreground operators:
% 5.79/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.79/2.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.79/2.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.79/2.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.79/2.21  tff('#skF_2', type, '#skF_2': $i).
% 5.79/2.21  tff('#skF_1', type, '#skF_1': $i).
% 5.79/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.79/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.79/2.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.79/2.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.79/2.21  
% 5.79/2.22  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.79/2.22  tff(f_35, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 5.79/2.22  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.79/2.22  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.79/2.22  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.79/2.22  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_xboole_1)).
% 5.79/2.22  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 5.79/2.22  tff(f_50, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.79/2.22  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.79/2.22  tff(c_280, plain, (![A_38, B_39]: (k4_xboole_0(k2_xboole_0(A_38, B_39), B_39)=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.79/2.22  tff(c_293, plain, (![A_38]: (k4_xboole_0(A_38, k1_xboole_0)=k2_xboole_0(A_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_280, c_8])).
% 5.79/2.22  tff(c_309, plain, (![A_38]: (k2_xboole_0(A_38, k1_xboole_0)=A_38)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_293])).
% 5.79/2.22  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.79/2.22  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.79/2.22  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.79/2.22  tff(c_171, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.79/2.22  tff(c_189, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_171])).
% 5.79/2.22  tff(c_192, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_189])).
% 5.79/2.22  tff(c_595, plain, (![A_49, B_50, C_51]: (k3_xboole_0(k4_xboole_0(A_49, B_50), k4_xboole_0(A_49, C_51))=k4_xboole_0(A_49, k2_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.79/2.22  tff(c_657, plain, (![A_6, B_50]: (k4_xboole_0(A_6, k2_xboole_0(B_50, k1_xboole_0))=k3_xboole_0(k4_xboole_0(A_6, B_50), A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_595])).
% 5.79/2.22  tff(c_1083, plain, (![A_66, B_67]: (k3_xboole_0(k4_xboole_0(A_66, B_67), A_66)=k4_xboole_0(A_66, B_67))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_657])).
% 5.79/2.22  tff(c_1095, plain, (![A_66, B_67]: (k4_xboole_0(k4_xboole_0(A_66, B_67), k4_xboole_0(A_66, B_67))=k4_xboole_0(k4_xboole_0(A_66, B_67), A_66))), inference(superposition, [status(thm), theory('equality')], [c_1083, c_12])).
% 5.79/2.22  tff(c_1150, plain, (![A_68, B_69]: (k4_xboole_0(k4_xboole_0(A_68, B_69), A_68)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_192, c_1095])).
% 5.79/2.22  tff(c_1320, plain, (![A_72, B_73]: (k4_xboole_0(k3_xboole_0(A_72, B_73), A_72)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_1150])).
% 5.79/2.22  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.79/2.22  tff(c_1346, plain, (![A_72, B_73]: (k2_xboole_0(k4_xboole_0(A_72, k3_xboole_0(A_72, B_73)), k1_xboole_0)=k5_xboole_0(A_72, k3_xboole_0(A_72, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_1320, c_4])).
% 5.79/2.22  tff(c_1405, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k4_xboole_0(A_72, B_73))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_12, c_1346])).
% 5.79/2.22  tff(c_24, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.79/2.22  tff(c_9587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1405, c_24])).
% 5.79/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.79/2.22  
% 5.79/2.22  Inference rules
% 5.79/2.22  ----------------------
% 5.79/2.22  #Ref     : 0
% 5.79/2.22  #Sup     : 2394
% 5.79/2.22  #Fact    : 0
% 5.79/2.22  #Define  : 0
% 5.79/2.22  #Split   : 0
% 5.79/2.22  #Chain   : 0
% 5.79/2.22  #Close   : 0
% 5.79/2.22  
% 5.79/2.22  Ordering : KBO
% 5.79/2.22  
% 5.79/2.22  Simplification rules
% 5.79/2.22  ----------------------
% 5.79/2.22  #Subsume      : 0
% 5.79/2.22  #Demod        : 2714
% 5.79/2.22  #Tautology    : 1721
% 5.79/2.22  #SimpNegUnit  : 0
% 5.79/2.22  #BackRed      : 2
% 5.79/2.22  
% 5.79/2.22  #Partial instantiations: 0
% 5.79/2.22  #Strategies tried      : 1
% 5.79/2.22  
% 5.79/2.22  Timing (in seconds)
% 5.79/2.22  ----------------------
% 5.79/2.23  Preprocessing        : 0.29
% 5.79/2.23  Parsing              : 0.15
% 5.79/2.23  CNF conversion       : 0.02
% 5.79/2.23  Main loop            : 1.17
% 5.79/2.23  Inferencing          : 0.35
% 5.79/2.23  Reduction            : 0.57
% 5.79/2.23  Demodulation         : 0.48
% 5.79/2.23  BG Simplification    : 0.04
% 5.79/2.23  Subsumption          : 0.14
% 5.79/2.23  Abstraction          : 0.07
% 5.79/2.23  MUC search           : 0.00
% 5.79/2.23  Cooper               : 0.00
% 5.79/2.23  Total                : 1.49
% 5.79/2.23  Index Insertion      : 0.00
% 5.79/2.23  Index Deletion       : 0.00
% 5.79/2.23  Index Matching       : 0.00
% 5.79/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
