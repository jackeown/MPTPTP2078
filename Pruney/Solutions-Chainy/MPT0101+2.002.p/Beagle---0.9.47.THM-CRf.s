%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:39 EST 2020

% Result     : Theorem 8.77s
% Output     : CNFRefutation 8.81s
% Verified   : 
% Statistics : Number of formulae       :   47 (  60 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  50 expanded)
%              Number of equality atoms :   36 (  49 expanded)
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

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(c_22,plain,(
    ! [A_24] : k4_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_176,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k2_xboole_0(A_48,B_49)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_251,plain,(
    ! [B_53,A_54] : k4_xboole_0(B_53,k2_xboole_0(A_54,B_53)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_176])).

tff(c_1188,plain,(
    ! [A_82,B_83] : k4_xboole_0(k3_xboole_0(A_82,B_83),A_82) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_251])).

tff(c_28,plain,(
    ! [A_29,B_30,C_31] : k4_xboole_0(k3_xboole_0(A_29,B_30),C_31) = k3_xboole_0(A_29,k4_xboole_0(B_30,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1193,plain,(
    ! [A_82,B_83] : k3_xboole_0(A_82,k4_xboole_0(B_83,A_82)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1188,c_28])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_22,B_23] : k2_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),k4_xboole_0(B_6,A_5)) = k5_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_32,B_33] : k4_xboole_0(k2_xboole_0(A_32,B_33),k3_xboole_0(A_32,B_33)) = k2_xboole_0(k4_xboole_0(A_32,B_33),k4_xboole_0(B_33,A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1108,plain,(
    ! [A_80,B_81] : k4_xboole_0(k2_xboole_0(A_80,B_81),k3_xboole_0(A_80,B_81)) = k5_xboole_0(A_80,B_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_30])).

tff(c_6122,plain,(
    ! [A_166,B_167] : k4_xboole_0(k2_xboole_0(A_166,B_167),k3_xboole_0(B_167,A_166)) = k5_xboole_0(A_166,B_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1108])).

tff(c_6250,plain,(
    ! [A_22,B_23] : k4_xboole_0(k2_xboole_0(A_22,B_23),k3_xboole_0(k4_xboole_0(B_23,A_22),A_22)) = k5_xboole_0(A_22,k4_xboole_0(B_23,A_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_6122])).

tff(c_6309,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1193,c_4,c_6250])).

tff(c_26,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k3_xboole_0(A_27,B_28)) = k4_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1156,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k3_xboole_0(A_11,k3_xboole_0(A_11,B_12))) = k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1108])).

tff(c_2916,plain,(
    ! [A_116,B_117] : k5_xboole_0(A_116,k3_xboole_0(A_116,B_117)) = k4_xboole_0(A_116,B_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_1156])).

tff(c_2986,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = k4_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2916])).

tff(c_32,plain,(
    ! [A_34,B_35,C_36] : k5_xboole_0(k5_xboole_0(A_34,B_35),C_36) = k5_xboole_0(A_34,k5_xboole_0(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_35,plain,(
    k5_xboole_0('#skF_1',k5_xboole_0('#skF_2',k3_xboole_0('#skF_1','#skF_2'))) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_3282,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2986,c_35])).

tff(c_21962,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6309,c_3282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.77/3.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.81/3.48  
% 8.81/3.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.81/3.48  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 8.81/3.48  
% 8.81/3.48  %Foreground sorts:
% 8.81/3.48  
% 8.81/3.48  
% 8.81/3.48  %Background operators:
% 8.81/3.48  
% 8.81/3.48  
% 8.81/3.48  %Foreground operators:
% 8.81/3.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.81/3.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.81/3.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.81/3.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.81/3.48  tff('#skF_2', type, '#skF_2': $i).
% 8.81/3.48  tff('#skF_1', type, '#skF_1': $i).
% 8.81/3.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.81/3.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.81/3.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.81/3.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.81/3.48  
% 8.81/3.49  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.81/3.49  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 8.81/3.49  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.81/3.49  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 8.81/3.49  tff(f_53, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 8.81/3.49  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.81/3.49  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.81/3.49  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 8.81/3.49  tff(f_55, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_xboole_1)).
% 8.81/3.49  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.81/3.49  tff(f_57, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.81/3.49  tff(f_60, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 8.81/3.49  tff(c_22, plain, (![A_24]: (k4_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.81/3.49  tff(c_12, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k3_xboole_0(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.81/3.49  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.81/3.49  tff(c_176, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k2_xboole_0(A_48, B_49))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.81/3.49  tff(c_251, plain, (![B_53, A_54]: (k4_xboole_0(B_53, k2_xboole_0(A_54, B_53))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_176])).
% 8.81/3.49  tff(c_1188, plain, (![A_82, B_83]: (k4_xboole_0(k3_xboole_0(A_82, B_83), A_82)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_251])).
% 8.81/3.49  tff(c_28, plain, (![A_29, B_30, C_31]: (k4_xboole_0(k3_xboole_0(A_29, B_30), C_31)=k3_xboole_0(A_29, k4_xboole_0(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.81/3.49  tff(c_1193, plain, (![A_82, B_83]: (k3_xboole_0(A_82, k4_xboole_0(B_83, A_82))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1188, c_28])).
% 8.81/3.49  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.81/3.49  tff(c_20, plain, (![A_22, B_23]: (k2_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.81/3.49  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), k4_xboole_0(B_6, A_5))=k5_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.81/3.49  tff(c_30, plain, (![A_32, B_33]: (k4_xboole_0(k2_xboole_0(A_32, B_33), k3_xboole_0(A_32, B_33))=k2_xboole_0(k4_xboole_0(A_32, B_33), k4_xboole_0(B_33, A_32)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.81/3.49  tff(c_1108, plain, (![A_80, B_81]: (k4_xboole_0(k2_xboole_0(A_80, B_81), k3_xboole_0(A_80, B_81))=k5_xboole_0(A_80, B_81))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_30])).
% 8.81/3.49  tff(c_6122, plain, (![A_166, B_167]: (k4_xboole_0(k2_xboole_0(A_166, B_167), k3_xboole_0(B_167, A_166))=k5_xboole_0(A_166, B_167))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1108])).
% 8.81/3.49  tff(c_6250, plain, (![A_22, B_23]: (k4_xboole_0(k2_xboole_0(A_22, B_23), k3_xboole_0(k4_xboole_0(B_23, A_22), A_22))=k5_xboole_0(A_22, k4_xboole_0(B_23, A_22)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_6122])).
% 8.81/3.49  tff(c_6309, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1193, c_4, c_6250])).
% 8.81/3.49  tff(c_26, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k3_xboole_0(A_27, B_28))=k4_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.81/3.49  tff(c_1156, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k3_xboole_0(A_11, k3_xboole_0(A_11, B_12)))=k5_xboole_0(A_11, k3_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1108])).
% 8.81/3.49  tff(c_2916, plain, (![A_116, B_117]: (k5_xboole_0(A_116, k3_xboole_0(A_116, B_117))=k4_xboole_0(A_116, B_117))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_1156])).
% 8.81/3.49  tff(c_2986, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(B_4, A_3))=k4_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2916])).
% 8.81/3.49  tff(c_32, plain, (![A_34, B_35, C_36]: (k5_xboole_0(k5_xboole_0(A_34, B_35), C_36)=k5_xboole_0(A_34, k5_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.81/3.49  tff(c_34, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.81/3.49  tff(c_35, plain, (k5_xboole_0('#skF_1', k5_xboole_0('#skF_2', k3_xboole_0('#skF_1', '#skF_2')))!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 8.81/3.49  tff(c_3282, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2986, c_35])).
% 8.81/3.49  tff(c_21962, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6309, c_3282])).
% 8.81/3.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.81/3.49  
% 8.81/3.49  Inference rules
% 8.81/3.49  ----------------------
% 8.81/3.49  #Ref     : 0
% 8.81/3.49  #Sup     : 5546
% 8.81/3.49  #Fact    : 0
% 8.81/3.49  #Define  : 0
% 8.81/3.49  #Split   : 0
% 8.81/3.49  #Chain   : 0
% 8.81/3.49  #Close   : 0
% 8.81/3.49  
% 8.81/3.49  Ordering : KBO
% 8.81/3.49  
% 8.81/3.49  Simplification rules
% 8.81/3.49  ----------------------
% 8.81/3.49  #Subsume      : 25
% 8.81/3.49  #Demod        : 6090
% 8.81/3.49  #Tautology    : 3686
% 8.81/3.49  #SimpNegUnit  : 0
% 8.81/3.49  #BackRed      : 3
% 8.81/3.49  
% 8.81/3.49  #Partial instantiations: 0
% 8.81/3.49  #Strategies tried      : 1
% 8.81/3.49  
% 8.81/3.49  Timing (in seconds)
% 8.81/3.49  ----------------------
% 8.81/3.49  Preprocessing        : 0.31
% 8.81/3.49  Parsing              : 0.16
% 8.81/3.49  CNF conversion       : 0.02
% 8.81/3.49  Main loop            : 2.42
% 8.81/3.49  Inferencing          : 0.52
% 8.81/3.49  Reduction            : 1.39
% 8.81/3.49  Demodulation         : 1.24
% 8.81/3.49  BG Simplification    : 0.07
% 8.81/3.49  Subsumption          : 0.32
% 8.81/3.49  Abstraction          : 0.12
% 8.81/3.49  MUC search           : 0.00
% 8.81/3.49  Cooper               : 0.00
% 8.81/3.49  Total                : 2.76
% 8.81/3.49  Index Insertion      : 0.00
% 8.81/3.50  Index Deletion       : 0.00
% 8.81/3.50  Index Matching       : 0.00
% 8.81/3.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
