%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:38 EST 2020

% Result     : Theorem 35.76s
% Output     : CNFRefutation 35.77s
% Verified   : 
% Statistics : Number of formulae       :   42 (  64 expanded)
%              Number of leaves         :   18 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  56 expanded)
%              Number of equality atoms :   29 (  51 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_405,plain,(
    ! [A_53,B_54,C_55] : k2_xboole_0(k2_xboole_0(A_53,B_54),C_55) = k2_xboole_0(A_53,k2_xboole_0(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7523,plain,(
    ! [A_186,B_187,C_188] : k2_xboole_0(k4_xboole_0(A_186,B_187),k2_xboole_0(k4_xboole_0(B_187,A_186),C_188)) = k2_xboole_0(k5_xboole_0(A_186,B_187),C_188) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_405])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2463,plain,(
    ! [A_108,B_109,C_110] : k2_xboole_0(k2_xboole_0(A_108,B_109),C_110) = k2_xboole_0(B_109,k2_xboole_0(A_108,C_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_405])).

tff(c_2565,plain,(
    ! [C_110,A_108,B_109] : k2_xboole_0(C_110,k2_xboole_0(A_108,B_109)) = k2_xboole_0(B_109,k2_xboole_0(A_108,C_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2463,c_2])).

tff(c_7541,plain,(
    ! [C_188,B_187,A_186] : k2_xboole_0(C_188,k2_xboole_0(k4_xboole_0(B_187,A_186),k4_xboole_0(A_186,B_187))) = k2_xboole_0(k5_xboole_0(A_186,B_187),C_188) ),
    inference(superposition,[status(thm),theory(equality)],[c_7523,c_2565])).

tff(c_7835,plain,(
    ! [A_186,B_187,C_188] : k2_xboole_0(k5_xboole_0(A_186,B_187),C_188) = k2_xboole_0(C_188,k5_xboole_0(B_187,A_186)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_7541])).

tff(c_10,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    ! [A_25,B_26] :
      ( k2_xboole_0(A_25,B_26) = B_26
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_61,plain,(
    ! [A_27,B_28] : k2_xboole_0(k3_xboole_0(A_27,B_28),A_27) = A_27 ),
    inference(resolution,[status(thm)],[c_8,c_56])).

tff(c_67,plain,(
    ! [A_27,B_28] : k2_xboole_0(A_27,k3_xboole_0(A_27,B_28)) = A_27 ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_2])).

tff(c_14,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_126,plain,(
    ! [A_35,B_36] : k2_xboole_0(A_35,k4_xboole_0(B_36,A_35)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_138,plain,(
    ! [A_14,B_15] : k2_xboole_0(k3_xboole_0(A_14,B_15),k4_xboole_0(A_14,B_15)) = k2_xboole_0(k3_xboole_0(A_14,B_15),A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_126])).

tff(c_142,plain,(
    ! [A_14,B_15] : k2_xboole_0(k3_xboole_0(A_14,B_15),k4_xboole_0(A_14,B_15)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_2,c_138])).

tff(c_88603,plain,(
    ! [A_590,B_591,A_592] : k2_xboole_0(k4_xboole_0(A_590,B_591),k2_xboole_0(A_592,k4_xboole_0(B_591,A_590))) = k2_xboole_0(k5_xboole_0(A_590,B_591),A_592) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7523])).

tff(c_89336,plain,(
    ! [B_15,A_14] : k2_xboole_0(k5_xboole_0(B_15,A_14),k3_xboole_0(A_14,B_15)) = k2_xboole_0(k4_xboole_0(B_15,A_14),A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_88603])).

tff(c_89559,plain,(
    ! [B_593,A_594] : k2_xboole_0(k5_xboole_0(B_593,A_594),k3_xboole_0(A_594,B_593)) = k2_xboole_0(A_594,B_593) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2,c_89336])).

tff(c_89910,plain,(
    ! [B_187,A_186] : k2_xboole_0(k3_xboole_0(B_187,A_186),k5_xboole_0(B_187,A_186)) = k2_xboole_0(B_187,A_186) ),
    inference(superposition,[status(thm),theory(equality)],[c_7835,c_89559])).

tff(c_20,plain,(
    k2_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_21,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_91518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89910,c_21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:04 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 35.76/25.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.77/25.93  
% 35.77/25.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.77/25.94  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 35.77/25.94  
% 35.77/25.94  %Foreground sorts:
% 35.77/25.94  
% 35.77/25.94  
% 35.77/25.94  %Background operators:
% 35.77/25.94  
% 35.77/25.94  
% 35.77/25.94  %Foreground operators:
% 35.77/25.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 35.77/25.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 35.77/25.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 35.77/25.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 35.77/25.94  tff('#skF_2', type, '#skF_2': $i).
% 35.77/25.94  tff('#skF_1', type, '#skF_1': $i).
% 35.77/25.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 35.77/25.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 35.77/25.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 35.77/25.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 35.77/25.94  
% 35.77/25.95  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 35.77/25.95  tff(f_45, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 35.77/25.95  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 35.77/25.95  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 35.77/25.95  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 35.77/25.95  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 35.77/25.95  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 35.77/25.95  tff(f_48, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 35.77/25.95  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 35.77/25.95  tff(c_405, plain, (![A_53, B_54, C_55]: (k2_xboole_0(k2_xboole_0(A_53, B_54), C_55)=k2_xboole_0(A_53, k2_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 35.77/25.95  tff(c_7523, plain, (![A_186, B_187, C_188]: (k2_xboole_0(k4_xboole_0(A_186, B_187), k2_xboole_0(k4_xboole_0(B_187, A_186), C_188))=k2_xboole_0(k5_xboole_0(A_186, B_187), C_188))), inference(superposition, [status(thm), theory('equality')], [c_4, c_405])).
% 35.77/25.95  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 35.77/25.95  tff(c_2463, plain, (![A_108, B_109, C_110]: (k2_xboole_0(k2_xboole_0(A_108, B_109), C_110)=k2_xboole_0(B_109, k2_xboole_0(A_108, C_110)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_405])).
% 35.77/25.95  tff(c_2565, plain, (![C_110, A_108, B_109]: (k2_xboole_0(C_110, k2_xboole_0(A_108, B_109))=k2_xboole_0(B_109, k2_xboole_0(A_108, C_110)))), inference(superposition, [status(thm), theory('equality')], [c_2463, c_2])).
% 35.77/25.95  tff(c_7541, plain, (![C_188, B_187, A_186]: (k2_xboole_0(C_188, k2_xboole_0(k4_xboole_0(B_187, A_186), k4_xboole_0(A_186, B_187)))=k2_xboole_0(k5_xboole_0(A_186, B_187), C_188))), inference(superposition, [status(thm), theory('equality')], [c_7523, c_2565])).
% 35.77/25.95  tff(c_7835, plain, (![A_186, B_187, C_188]: (k2_xboole_0(k5_xboole_0(A_186, B_187), C_188)=k2_xboole_0(C_188, k5_xboole_0(B_187, A_186)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_7541])).
% 35.77/25.95  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 35.77/25.95  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 35.77/25.95  tff(c_56, plain, (![A_25, B_26]: (k2_xboole_0(A_25, B_26)=B_26 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 35.77/25.95  tff(c_61, plain, (![A_27, B_28]: (k2_xboole_0(k3_xboole_0(A_27, B_28), A_27)=A_27)), inference(resolution, [status(thm)], [c_8, c_56])).
% 35.77/25.95  tff(c_67, plain, (![A_27, B_28]: (k2_xboole_0(A_27, k3_xboole_0(A_27, B_28))=A_27)), inference(superposition, [status(thm), theory('equality')], [c_61, c_2])).
% 35.77/25.95  tff(c_14, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 35.77/25.95  tff(c_126, plain, (![A_35, B_36]: (k2_xboole_0(A_35, k4_xboole_0(B_36, A_35))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_37])).
% 35.77/25.95  tff(c_138, plain, (![A_14, B_15]: (k2_xboole_0(k3_xboole_0(A_14, B_15), k4_xboole_0(A_14, B_15))=k2_xboole_0(k3_xboole_0(A_14, B_15), A_14))), inference(superposition, [status(thm), theory('equality')], [c_14, c_126])).
% 35.77/25.95  tff(c_142, plain, (![A_14, B_15]: (k2_xboole_0(k3_xboole_0(A_14, B_15), k4_xboole_0(A_14, B_15))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_67, c_2, c_138])).
% 35.77/25.95  tff(c_88603, plain, (![A_590, B_591, A_592]: (k2_xboole_0(k4_xboole_0(A_590, B_591), k2_xboole_0(A_592, k4_xboole_0(B_591, A_590)))=k2_xboole_0(k5_xboole_0(A_590, B_591), A_592))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7523])).
% 35.77/25.95  tff(c_89336, plain, (![B_15, A_14]: (k2_xboole_0(k5_xboole_0(B_15, A_14), k3_xboole_0(A_14, B_15))=k2_xboole_0(k4_xboole_0(B_15, A_14), A_14))), inference(superposition, [status(thm), theory('equality')], [c_142, c_88603])).
% 35.77/25.95  tff(c_89559, plain, (![B_593, A_594]: (k2_xboole_0(k5_xboole_0(B_593, A_594), k3_xboole_0(A_594, B_593))=k2_xboole_0(A_594, B_593))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2, c_89336])).
% 35.77/25.95  tff(c_89910, plain, (![B_187, A_186]: (k2_xboole_0(k3_xboole_0(B_187, A_186), k5_xboole_0(B_187, A_186))=k2_xboole_0(B_187, A_186))), inference(superposition, [status(thm), theory('equality')], [c_7835, c_89559])).
% 35.77/25.95  tff(c_20, plain, (k2_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 35.77/25.95  tff(c_21, plain, (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 35.77/25.95  tff(c_91518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89910, c_21])).
% 35.77/25.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.77/25.95  
% 35.77/25.95  Inference rules
% 35.77/25.95  ----------------------
% 35.77/25.95  #Ref     : 0
% 35.77/25.95  #Sup     : 23083
% 35.77/25.95  #Fact    : 0
% 35.77/25.95  #Define  : 0
% 35.77/25.95  #Split   : 0
% 35.77/25.95  #Chain   : 0
% 35.77/25.95  #Close   : 0
% 35.77/25.95  
% 35.77/25.95  Ordering : KBO
% 35.77/25.95  
% 35.77/25.95  Simplification rules
% 35.77/25.95  ----------------------
% 35.77/25.95  #Subsume      : 1336
% 35.77/25.95  #Demod        : 27203
% 35.77/25.95  #Tautology    : 7927
% 35.77/25.95  #SimpNegUnit  : 0
% 35.77/25.95  #BackRed      : 26
% 35.77/25.95  
% 35.77/25.95  #Partial instantiations: 0
% 35.77/25.95  #Strategies tried      : 1
% 35.77/25.95  
% 35.77/25.95  Timing (in seconds)
% 35.77/25.95  ----------------------
% 35.77/25.95  Preprocessing        : 0.30
% 35.77/25.95  Parsing              : 0.16
% 35.77/25.95  CNF conversion       : 0.02
% 35.77/25.95  Main loop            : 24.85
% 35.77/25.95  Inferencing          : 2.43
% 35.77/25.95  Reduction            : 18.71
% 35.77/25.95  Demodulation         : 18.02
% 35.77/25.95  BG Simplification    : 0.43
% 35.77/25.95  Subsumption          : 2.71
% 35.77/25.95  Abstraction          : 0.76
% 35.77/25.95  MUC search           : 0.00
% 35.77/25.95  Cooper               : 0.00
% 35.77/25.95  Total                : 25.17
% 35.77/25.95  Index Insertion      : 0.00
% 35.77/25.95  Index Deletion       : 0.00
% 35.77/25.95  Index Matching       : 0.00
% 35.77/25.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
