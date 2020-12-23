%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:50 EST 2020

% Result     : Theorem 4.79s
% Output     : CNFRefutation 4.79s
% Verified   : 
% Statistics : Number of formulae       :   48 (  69 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :   38 (  59 expanded)
%              Number of equality atoms :   37 (  58 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_120,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_99])).

tff(c_287,plain,(
    ! [A_39,B_40,C_41] : k4_xboole_0(k4_xboole_0(A_39,B_40),C_41) = k4_xboole_0(A_39,k2_xboole_0(B_40,C_41)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_335,plain,(
    ! [A_5,C_41] : k4_xboole_0(k3_xboole_0(A_5,k1_xboole_0),C_41) = k4_xboole_0(A_5,k2_xboole_0(A_5,C_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_287])).

tff(c_372,plain,(
    ! [A_42,C_43] : k4_xboole_0(k3_xboole_0(A_42,k1_xboole_0),C_43) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_335])).

tff(c_402,plain,(
    ! [A_42] : k3_xboole_0(A_42,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_6])).

tff(c_584,plain,(
    ! [A_48] : k4_xboole_0(A_48,A_48) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_120])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k4_xboole_0(k4_xboole_0(A_6,B_7),C_8) = k4_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_596,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k2_xboole_0(B_7,k4_xboole_0(A_6,B_7))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_8])).

tff(c_623,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k2_xboole_0(B_7,A_6)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_596])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_311,plain,(
    ! [C_41,A_39,B_40] : k2_xboole_0(C_41,k4_xboole_0(A_39,k2_xboole_0(B_40,C_41))) = k2_xboole_0(C_41,k4_xboole_0(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_4])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_346,plain,(
    ! [A_39,B_40,B_12] : k4_xboole_0(A_39,k2_xboole_0(B_40,k4_xboole_0(k4_xboole_0(A_39,B_40),B_12))) = k3_xboole_0(k4_xboole_0(A_39,B_40),B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_287])).

tff(c_5905,plain,(
    ! [A_151,B_152,B_153] : k4_xboole_0(A_151,k2_xboole_0(B_152,k4_xboole_0(A_151,k2_xboole_0(B_152,B_153)))) = k3_xboole_0(k4_xboole_0(A_151,B_152),B_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_346])).

tff(c_6069,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k2_xboole_0(B_40,k4_xboole_0(A_39,B_40))) = k3_xboole_0(k4_xboole_0(A_39,B_40),B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_5905])).

tff(c_6202,plain,(
    ! [B_154,A_155] : k3_xboole_0(B_154,k4_xboole_0(A_155,B_154)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_4,c_2,c_6069])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] : k5_xboole_0(k5_xboole_0(A_14,B_15),C_16) = k5_xboole_0(A_14,k5_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_533,plain,(
    ! [A_46,B_47] : k5_xboole_0(k5_xboole_0(A_46,B_47),k3_xboole_0(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_564,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k5_xboole_0(B_15,k3_xboole_0(A_14,B_15))) = k2_xboole_0(A_14,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_533])).

tff(c_6243,plain,(
    ! [B_154,A_155] : k5_xboole_0(B_154,k5_xboole_0(k4_xboole_0(A_155,B_154),k1_xboole_0)) = k2_xboole_0(B_154,k4_xboole_0(A_155,B_154)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6202,c_564])).

tff(c_6339,plain,(
    ! [B_154,A_155] : k5_xboole_0(B_154,k4_xboole_0(A_155,B_154)) = k2_xboole_0(B_154,A_155) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_14,c_6243])).

tff(c_20,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_7409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6339,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.79/1.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.94  
% 4.79/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.94  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 4.79/1.94  
% 4.79/1.94  %Foreground sorts:
% 4.79/1.94  
% 4.79/1.94  
% 4.79/1.94  %Background operators:
% 4.79/1.94  
% 4.79/1.94  
% 4.79/1.94  %Foreground operators:
% 4.79/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.79/1.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.79/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.79/1.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.79/1.94  tff('#skF_2', type, '#skF_2': $i).
% 4.79/1.94  tff('#skF_1', type, '#skF_1': $i).
% 4.79/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.79/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.79/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.79/1.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.79/1.94  
% 4.79/1.96  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.79/1.96  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.79/1.96  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.79/1.96  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.79/1.96  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.79/1.96  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.79/1.96  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.79/1.96  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.79/1.96  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.79/1.96  tff(f_46, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.79/1.96  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.79/1.96  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.79/1.96  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.79/1.96  tff(c_6, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.79/1.96  tff(c_99, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.79/1.96  tff(c_120, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_99])).
% 4.79/1.96  tff(c_287, plain, (![A_39, B_40, C_41]: (k4_xboole_0(k4_xboole_0(A_39, B_40), C_41)=k4_xboole_0(A_39, k2_xboole_0(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.79/1.96  tff(c_335, plain, (![A_5, C_41]: (k4_xboole_0(k3_xboole_0(A_5, k1_xboole_0), C_41)=k4_xboole_0(A_5, k2_xboole_0(A_5, C_41)))), inference(superposition, [status(thm), theory('equality')], [c_120, c_287])).
% 4.79/1.96  tff(c_372, plain, (![A_42, C_43]: (k4_xboole_0(k3_xboole_0(A_42, k1_xboole_0), C_43)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_335])).
% 4.79/1.96  tff(c_402, plain, (![A_42]: (k3_xboole_0(A_42, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_372, c_6])).
% 4.79/1.96  tff(c_584, plain, (![A_48]: (k4_xboole_0(A_48, A_48)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_402, c_120])).
% 4.79/1.96  tff(c_8, plain, (![A_6, B_7, C_8]: (k4_xboole_0(k4_xboole_0(A_6, B_7), C_8)=k4_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.79/1.96  tff(c_596, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k2_xboole_0(B_7, k4_xboole_0(A_6, B_7)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_584, c_8])).
% 4.79/1.96  tff(c_623, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k2_xboole_0(B_7, A_6))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_596])).
% 4.79/1.96  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.79/1.96  tff(c_311, plain, (![C_41, A_39, B_40]: (k2_xboole_0(C_41, k4_xboole_0(A_39, k2_xboole_0(B_40, C_41)))=k2_xboole_0(C_41, k4_xboole_0(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_287, c_4])).
% 4.79/1.96  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.79/1.96  tff(c_346, plain, (![A_39, B_40, B_12]: (k4_xboole_0(A_39, k2_xboole_0(B_40, k4_xboole_0(k4_xboole_0(A_39, B_40), B_12)))=k3_xboole_0(k4_xboole_0(A_39, B_40), B_12))), inference(superposition, [status(thm), theory('equality')], [c_12, c_287])).
% 4.79/1.96  tff(c_5905, plain, (![A_151, B_152, B_153]: (k4_xboole_0(A_151, k2_xboole_0(B_152, k4_xboole_0(A_151, k2_xboole_0(B_152, B_153))))=k3_xboole_0(k4_xboole_0(A_151, B_152), B_153))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_346])).
% 4.79/1.96  tff(c_6069, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k2_xboole_0(B_40, k4_xboole_0(A_39, B_40)))=k3_xboole_0(k4_xboole_0(A_39, B_40), B_40))), inference(superposition, [status(thm), theory('equality')], [c_311, c_5905])).
% 4.79/1.96  tff(c_6202, plain, (![B_154, A_155]: (k3_xboole_0(B_154, k4_xboole_0(A_155, B_154))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_623, c_4, c_2, c_6069])).
% 4.79/1.96  tff(c_16, plain, (![A_14, B_15, C_16]: (k5_xboole_0(k5_xboole_0(A_14, B_15), C_16)=k5_xboole_0(A_14, k5_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.79/1.96  tff(c_533, plain, (![A_46, B_47]: (k5_xboole_0(k5_xboole_0(A_46, B_47), k3_xboole_0(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.79/1.96  tff(c_564, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k5_xboole_0(B_15, k3_xboole_0(A_14, B_15)))=k2_xboole_0(A_14, B_15))), inference(superposition, [status(thm), theory('equality')], [c_16, c_533])).
% 4.79/1.96  tff(c_6243, plain, (![B_154, A_155]: (k5_xboole_0(B_154, k5_xboole_0(k4_xboole_0(A_155, B_154), k1_xboole_0))=k2_xboole_0(B_154, k4_xboole_0(A_155, B_154)))), inference(superposition, [status(thm), theory('equality')], [c_6202, c_564])).
% 4.79/1.96  tff(c_6339, plain, (![B_154, A_155]: (k5_xboole_0(B_154, k4_xboole_0(A_155, B_154))=k2_xboole_0(B_154, A_155))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_14, c_6243])).
% 4.79/1.96  tff(c_20, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.79/1.96  tff(c_7409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6339, c_20])).
% 4.79/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.96  
% 4.79/1.96  Inference rules
% 4.79/1.96  ----------------------
% 4.79/1.96  #Ref     : 0
% 4.79/1.96  #Sup     : 1801
% 4.79/1.96  #Fact    : 0
% 4.79/1.96  #Define  : 0
% 4.79/1.96  #Split   : 0
% 4.79/1.96  #Chain   : 0
% 4.79/1.96  #Close   : 0
% 4.79/1.96  
% 4.79/1.96  Ordering : KBO
% 4.79/1.96  
% 4.79/1.96  Simplification rules
% 4.79/1.96  ----------------------
% 4.79/1.96  #Subsume      : 5
% 4.79/1.96  #Demod        : 1853
% 4.79/1.96  #Tautology    : 1294
% 4.79/1.96  #SimpNegUnit  : 0
% 4.79/1.96  #BackRed      : 13
% 4.79/1.96  
% 4.79/1.96  #Partial instantiations: 0
% 4.79/1.96  #Strategies tried      : 1
% 4.79/1.96  
% 4.79/1.96  Timing (in seconds)
% 4.79/1.96  ----------------------
% 4.79/1.96  Preprocessing        : 0.26
% 4.79/1.96  Parsing              : 0.15
% 4.79/1.96  CNF conversion       : 0.02
% 4.79/1.96  Main loop            : 0.95
% 4.79/1.96  Inferencing          : 0.30
% 4.79/1.96  Reduction            : 0.45
% 4.79/1.96  Demodulation         : 0.37
% 4.79/1.96  BG Simplification    : 0.04
% 4.79/1.96  Subsumption          : 0.12
% 4.79/1.96  Abstraction          : 0.05
% 4.79/1.96  MUC search           : 0.00
% 4.79/1.96  Cooper               : 0.00
% 4.79/1.96  Total                : 1.24
% 4.79/1.96  Index Insertion      : 0.00
% 4.79/1.96  Index Deletion       : 0.00
% 4.79/1.96  Index Matching       : 0.00
% 4.79/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
