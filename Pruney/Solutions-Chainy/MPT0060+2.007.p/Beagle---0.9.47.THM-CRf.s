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
% DateTime   : Thu Dec  3 09:43:06 EST 2020

% Result     : Theorem 14.24s
% Output     : CNFRefutation 14.24s
% Verified   : 
% Statistics : Number of formulae       :   45 (  65 expanded)
%              Number of leaves         :   18 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   35 (  55 expanded)
%              Number of equality atoms :   34 (  54 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_97,plain,(
    ! [A_23,B_24] : k4_xboole_0(k2_xboole_0(A_23,B_24),B_24) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [A_23] : k4_xboole_0(A_23,k1_xboole_0) = k2_xboole_0(A_23,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_4])).

tff(c_122,plain,(
    ! [A_25] : k2_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_104])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_140,plain,(
    ! [A_25] : k4_xboole_0(A_25,A_25) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_10])).

tff(c_265,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_284,plain,(
    ! [A_25] : k4_xboole_0(A_25,k1_xboole_0) = k3_xboole_0(A_25,A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_265])).

tff(c_399,plain,(
    ! [A_36] : k3_xboole_0(A_36,A_36) = A_36 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_284])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k3_xboole_0(A_13,B_14),C_15) = k3_xboole_0(A_13,k4_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_405,plain,(
    ! [A_36,C_15] : k3_xboole_0(A_36,k4_xboole_0(A_36,C_15)) = k4_xboole_0(A_36,C_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_14])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k4_xboole_0(k4_xboole_0(A_6,B_7),C_8) = k4_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_113,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_97])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_469,plain,(
    ! [A_39,B_40,C_41] : k4_xboole_0(k4_xboole_0(A_39,B_40),C_41) = k4_xboole_0(A_39,k2_xboole_0(B_40,C_41)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_510,plain,(
    ! [A_11,B_12,C_41] : k4_xboole_0(A_11,k2_xboole_0(k4_xboole_0(A_11,B_12),C_41)) = k4_xboole_0(k3_xboole_0(A_11,B_12),C_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_469])).

tff(c_6770,plain,(
    ! [A_149,B_150,C_151] : k4_xboole_0(A_149,k2_xboole_0(k4_xboole_0(A_149,B_150),C_151)) = k3_xboole_0(A_149,k4_xboole_0(B_150,C_151)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_510])).

tff(c_50586,plain,(
    ! [A_448,A_449,B_450] : k4_xboole_0(A_448,k2_xboole_0(A_449,k4_xboole_0(A_448,B_450))) = k3_xboole_0(A_448,k4_xboole_0(B_450,A_449)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6770])).

tff(c_482,plain,(
    ! [A_39,B_40,B_12] : k4_xboole_0(A_39,k2_xboole_0(B_40,k4_xboole_0(k4_xboole_0(A_39,B_40),B_12))) = k3_xboole_0(k4_xboole_0(A_39,B_40),B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_469,c_12])).

tff(c_551,plain,(
    ! [A_39,B_40,B_12] : k4_xboole_0(A_39,k2_xboole_0(B_40,k4_xboole_0(A_39,k2_xboole_0(B_40,B_12)))) = k3_xboole_0(k4_xboole_0(A_39,B_40),B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_482])).

tff(c_50732,plain,(
    ! [A_448,A_449,B_12] : k3_xboole_0(A_448,k4_xboole_0(k2_xboole_0(A_449,B_12),A_449)) = k3_xboole_0(k4_xboole_0(A_448,A_449),B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_50586,c_551])).

tff(c_51291,plain,(
    ! [A_448,A_449,B_12] : k3_xboole_0(k4_xboole_0(A_448,A_449),B_12) = k3_xboole_0(A_448,k4_xboole_0(B_12,A_449)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_50732])).

tff(c_16,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).

tff(c_51416,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51291,c_17])).

tff(c_51424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_8,c_51416])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:21:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.24/6.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.24/6.73  
% 14.24/6.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.24/6.73  %$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 14.24/6.73  
% 14.24/6.73  %Foreground sorts:
% 14.24/6.73  
% 14.24/6.73  
% 14.24/6.73  %Background operators:
% 14.24/6.73  
% 14.24/6.73  
% 14.24/6.73  %Foreground operators:
% 14.24/6.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.24/6.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.24/6.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.24/6.73  tff('#skF_2', type, '#skF_2': $i).
% 14.24/6.73  tff('#skF_3', type, '#skF_3': $i).
% 14.24/6.73  tff('#skF_1', type, '#skF_1': $i).
% 14.24/6.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.24/6.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.24/6.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.24/6.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.24/6.73  
% 14.24/6.74  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 14.24/6.74  tff(f_31, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 14.24/6.74  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 14.24/6.74  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.24/6.74  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 14.24/6.74  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 14.24/6.74  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 14.24/6.74  tff(f_42, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 14.24/6.74  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.24/6.74  tff(c_97, plain, (![A_23, B_24]: (k4_xboole_0(k2_xboole_0(A_23, B_24), B_24)=k4_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.24/6.74  tff(c_104, plain, (![A_23]: (k4_xboole_0(A_23, k1_xboole_0)=k2_xboole_0(A_23, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_97, c_4])).
% 14.24/6.74  tff(c_122, plain, (![A_25]: (k2_xboole_0(A_25, k1_xboole_0)=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_104])).
% 14.24/6.74  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.24/6.74  tff(c_140, plain, (![A_25]: (k4_xboole_0(A_25, A_25)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_122, c_10])).
% 14.24/6.74  tff(c_265, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.24/6.74  tff(c_284, plain, (![A_25]: (k4_xboole_0(A_25, k1_xboole_0)=k3_xboole_0(A_25, A_25))), inference(superposition, [status(thm), theory('equality')], [c_140, c_265])).
% 14.24/6.74  tff(c_399, plain, (![A_36]: (k3_xboole_0(A_36, A_36)=A_36)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_284])).
% 14.24/6.74  tff(c_14, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k3_xboole_0(A_13, B_14), C_15)=k3_xboole_0(A_13, k4_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.24/6.74  tff(c_405, plain, (![A_36, C_15]: (k3_xboole_0(A_36, k4_xboole_0(A_36, C_15))=k4_xboole_0(A_36, C_15))), inference(superposition, [status(thm), theory('equality')], [c_399, c_14])).
% 14.24/6.74  tff(c_8, plain, (![A_6, B_7, C_8]: (k4_xboole_0(k4_xboole_0(A_6, B_7), C_8)=k4_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.24/6.74  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.24/6.74  tff(c_113, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_97])).
% 14.24/6.74  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.24/6.74  tff(c_469, plain, (![A_39, B_40, C_41]: (k4_xboole_0(k4_xboole_0(A_39, B_40), C_41)=k4_xboole_0(A_39, k2_xboole_0(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.24/6.74  tff(c_510, plain, (![A_11, B_12, C_41]: (k4_xboole_0(A_11, k2_xboole_0(k4_xboole_0(A_11, B_12), C_41))=k4_xboole_0(k3_xboole_0(A_11, B_12), C_41))), inference(superposition, [status(thm), theory('equality')], [c_12, c_469])).
% 14.24/6.74  tff(c_6770, plain, (![A_149, B_150, C_151]: (k4_xboole_0(A_149, k2_xboole_0(k4_xboole_0(A_149, B_150), C_151))=k3_xboole_0(A_149, k4_xboole_0(B_150, C_151)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_510])).
% 14.24/6.74  tff(c_50586, plain, (![A_448, A_449, B_450]: (k4_xboole_0(A_448, k2_xboole_0(A_449, k4_xboole_0(A_448, B_450)))=k3_xboole_0(A_448, k4_xboole_0(B_450, A_449)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_6770])).
% 14.24/6.74  tff(c_482, plain, (![A_39, B_40, B_12]: (k4_xboole_0(A_39, k2_xboole_0(B_40, k4_xboole_0(k4_xboole_0(A_39, B_40), B_12)))=k3_xboole_0(k4_xboole_0(A_39, B_40), B_12))), inference(superposition, [status(thm), theory('equality')], [c_469, c_12])).
% 14.24/6.74  tff(c_551, plain, (![A_39, B_40, B_12]: (k4_xboole_0(A_39, k2_xboole_0(B_40, k4_xboole_0(A_39, k2_xboole_0(B_40, B_12))))=k3_xboole_0(k4_xboole_0(A_39, B_40), B_12))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_482])).
% 14.24/6.74  tff(c_50732, plain, (![A_448, A_449, B_12]: (k3_xboole_0(A_448, k4_xboole_0(k2_xboole_0(A_449, B_12), A_449))=k3_xboole_0(k4_xboole_0(A_448, A_449), B_12))), inference(superposition, [status(thm), theory('equality')], [c_50586, c_551])).
% 14.24/6.74  tff(c_51291, plain, (![A_448, A_449, B_12]: (k3_xboole_0(k4_xboole_0(A_448, A_449), B_12)=k3_xboole_0(A_448, k4_xboole_0(B_12, A_449)))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_50732])).
% 14.24/6.74  tff(c_16, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.24/6.74  tff(c_17, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 14.24/6.74  tff(c_51416, plain, (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_51291, c_17])).
% 14.24/6.74  tff(c_51424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_405, c_8, c_51416])).
% 14.24/6.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.24/6.74  
% 14.24/6.74  Inference rules
% 14.24/6.74  ----------------------
% 14.24/6.74  #Ref     : 0
% 14.24/6.74  #Sup     : 12648
% 14.24/6.74  #Fact    : 0
% 14.24/6.74  #Define  : 0
% 14.24/6.74  #Split   : 0
% 14.24/6.74  #Chain   : 0
% 14.24/6.74  #Close   : 0
% 14.24/6.74  
% 14.24/6.74  Ordering : KBO
% 14.24/6.74  
% 14.24/6.74  Simplification rules
% 14.24/6.74  ----------------------
% 14.24/6.74  #Subsume      : 47
% 14.24/6.74  #Demod        : 15947
% 14.24/6.74  #Tautology    : 9000
% 14.24/6.74  #SimpNegUnit  : 0
% 14.24/6.74  #BackRed      : 10
% 14.24/6.74  
% 14.24/6.74  #Partial instantiations: 0
% 14.24/6.74  #Strategies tried      : 1
% 14.24/6.74  
% 14.24/6.74  Timing (in seconds)
% 14.24/6.74  ----------------------
% 14.24/6.75  Preprocessing        : 0.27
% 14.24/6.75  Parsing              : 0.14
% 14.24/6.75  CNF conversion       : 0.01
% 14.24/6.75  Main loop            : 5.73
% 14.24/6.75  Inferencing          : 0.97
% 14.24/6.75  Reduction            : 3.55
% 14.24/6.75  Demodulation         : 3.27
% 14.24/6.75  BG Simplification    : 0.11
% 14.24/6.75  Subsumption          : 0.87
% 14.24/6.75  Abstraction          : 0.23
% 14.24/6.75  MUC search           : 0.00
% 14.24/6.75  Cooper               : 0.00
% 14.24/6.75  Total                : 6.03
% 14.24/6.75  Index Insertion      : 0.00
% 14.24/6.75  Index Deletion       : 0.00
% 14.24/6.75  Index Matching       : 0.00
% 14.24/6.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
