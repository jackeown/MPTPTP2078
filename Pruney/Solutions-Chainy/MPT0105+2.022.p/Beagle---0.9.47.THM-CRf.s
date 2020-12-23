%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:50 EST 2020

% Result     : Theorem 4.58s
% Output     : CNFRefutation 4.58s
% Verified   : 
% Statistics : Number of formulae       :   56 (  88 expanded)
%              Number of leaves         :   24 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   45 (  77 expanded)
%              Number of equality atoms :   44 (  76 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_395,plain,(
    ! [A_61,B_62] : k4_xboole_0(k2_xboole_0(A_61,B_62),B_62) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_404,plain,(
    ! [B_62,A_61] : k2_xboole_0(B_62,k4_xboole_0(A_61,B_62)) = k2_xboole_0(B_62,k2_xboole_0(A_61,B_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_8])).

tff(c_429,plain,(
    ! [B_62,A_61] : k2_xboole_0(B_62,k2_xboole_0(A_61,B_62)) = k2_xboole_0(B_62,A_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_404])).

tff(c_24,plain,(
    ! [A_23] : k5_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_679,plain,(
    ! [A_71,B_72,C_73] : k4_xboole_0(k4_xboole_0(A_71,B_72),C_73) = k4_xboole_0(A_71,k2_xboole_0(B_72,C_73)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_156,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k2_xboole_0(A_42,B_43)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_166,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_156])).

tff(c_709,plain,(
    ! [A_71,B_72] : k4_xboole_0(A_71,k2_xboole_0(B_72,k4_xboole_0(A_71,B_72))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_679,c_166])).

tff(c_772,plain,(
    ! [A_71,B_72] : k4_xboole_0(A_71,k2_xboole_0(B_72,A_71)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_709])).

tff(c_18,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(k2_xboole_0(A_10,B_11),B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_436,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k4_xboole_0(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_470,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,k3_xboole_0(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_436])).

tff(c_3122,plain,(
    ! [A_140,B_141] : k3_xboole_0(A_140,k3_xboole_0(A_140,B_141)) = k3_xboole_0(A_140,B_141) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_470])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(k2_xboole_0(A_5,B_6),k3_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3143,plain,(
    ! [A_140,B_141] : k4_xboole_0(k2_xboole_0(A_140,k3_xboole_0(A_140,B_141)),k3_xboole_0(A_140,B_141)) = k5_xboole_0(A_140,k3_xboole_0(A_140,B_141)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3122,c_6])).

tff(c_3202,plain,(
    ! [A_140,B_141] : k5_xboole_0(A_140,k3_xboole_0(A_140,B_141)) = k4_xboole_0(A_140,B_141) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_12,c_3143])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_964,plain,(
    ! [A_80,B_81,C_82] : k5_xboole_0(k5_xboole_0(A_80,B_81),C_82) = k5_xboole_0(A_80,k5_xboole_0(B_81,C_82)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4435,plain,(
    ! [A_159,B_160,C_161] : k5_xboole_0(k5_xboole_0(A_159,B_160),C_161) = k5_xboole_0(B_160,k5_xboole_0(A_159,C_161)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_964])).

tff(c_34,plain,(
    ! [A_31,B_32] : k5_xboole_0(k5_xboole_0(A_31,B_32),k3_xboole_0(A_31,B_32)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4531,plain,(
    ! [B_160,A_159] : k5_xboole_0(B_160,k5_xboole_0(A_159,k3_xboole_0(A_159,B_160))) = k2_xboole_0(A_159,B_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_4435,c_34])).

tff(c_4859,plain,(
    ! [B_164,A_165] : k5_xboole_0(B_164,k4_xboole_0(A_165,B_164)) = k2_xboole_0(A_165,B_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3202,c_4531])).

tff(c_4956,plain,(
    ! [B_72,A_71] : k5_xboole_0(k2_xboole_0(B_72,A_71),k1_xboole_0) = k2_xboole_0(A_71,k2_xboole_0(B_72,A_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_772,c_4859])).

tff(c_5000,plain,(
    ! [B_72,A_71] : k2_xboole_0(B_72,A_71) = k2_xboole_0(A_71,B_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_24,c_4956])).

tff(c_4661,plain,(
    ! [B_160,A_159] : k5_xboole_0(B_160,k4_xboole_0(A_159,B_160)) = k2_xboole_0(A_159,B_160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3202,c_4531])).

tff(c_36,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4858,plain,(
    k2_xboole_0('#skF_2','#skF_1') != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4661,c_36])).

tff(c_5209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5000,c_4858])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.58/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.58/1.84  
% 4.58/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.58/1.85  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 4.58/1.85  
% 4.58/1.85  %Foreground sorts:
% 4.58/1.85  
% 4.58/1.85  
% 4.58/1.85  %Background operators:
% 4.58/1.85  
% 4.58/1.85  
% 4.58/1.85  %Foreground operators:
% 4.58/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.58/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.58/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.58/1.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.58/1.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.58/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.58/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.58/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.58/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.58/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.58/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.58/1.85  
% 4.58/1.86  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.58/1.86  tff(f_37, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.58/1.86  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.58/1.86  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.58/1.86  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.58/1.86  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.58/1.86  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.58/1.86  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.58/1.86  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 4.58/1.86  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.58/1.86  tff(f_57, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.58/1.86  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.58/1.86  tff(f_62, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.58/1.86  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.58/1.86  tff(c_395, plain, (![A_61, B_62]: (k4_xboole_0(k2_xboole_0(A_61, B_62), B_62)=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.58/1.86  tff(c_404, plain, (![B_62, A_61]: (k2_xboole_0(B_62, k4_xboole_0(A_61, B_62))=k2_xboole_0(B_62, k2_xboole_0(A_61, B_62)))), inference(superposition, [status(thm), theory('equality')], [c_395, c_8])).
% 4.58/1.86  tff(c_429, plain, (![B_62, A_61]: (k2_xboole_0(B_62, k2_xboole_0(A_61, B_62))=k2_xboole_0(B_62, A_61))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_404])).
% 4.58/1.86  tff(c_24, plain, (![A_23]: (k5_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.58/1.86  tff(c_679, plain, (![A_71, B_72, C_73]: (k4_xboole_0(k4_xboole_0(A_71, B_72), C_73)=k4_xboole_0(A_71, k2_xboole_0(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.58/1.86  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.58/1.86  tff(c_156, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k2_xboole_0(A_42, B_43))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.58/1.86  tff(c_166, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_156])).
% 4.58/1.86  tff(c_709, plain, (![A_71, B_72]: (k4_xboole_0(A_71, k2_xboole_0(B_72, k4_xboole_0(A_71, B_72)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_679, c_166])).
% 4.58/1.86  tff(c_772, plain, (![A_71, B_72]: (k4_xboole_0(A_71, k2_xboole_0(B_72, A_71))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_709])).
% 4.58/1.86  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.58/1.86  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(k2_xboole_0(A_10, B_11), B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.58/1.86  tff(c_20, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.58/1.86  tff(c_436, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k4_xboole_0(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.58/1.86  tff(c_470, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, k3_xboole_0(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_436])).
% 4.58/1.86  tff(c_3122, plain, (![A_140, B_141]: (k3_xboole_0(A_140, k3_xboole_0(A_140, B_141))=k3_xboole_0(A_140, B_141))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_470])).
% 4.58/1.86  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(k2_xboole_0(A_5, B_6), k3_xboole_0(A_5, B_6))=k5_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.58/1.86  tff(c_3143, plain, (![A_140, B_141]: (k4_xboole_0(k2_xboole_0(A_140, k3_xboole_0(A_140, B_141)), k3_xboole_0(A_140, B_141))=k5_xboole_0(A_140, k3_xboole_0(A_140, B_141)))), inference(superposition, [status(thm), theory('equality')], [c_3122, c_6])).
% 4.58/1.86  tff(c_3202, plain, (![A_140, B_141]: (k5_xboole_0(A_140, k3_xboole_0(A_140, B_141))=k4_xboole_0(A_140, B_141))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_12, c_3143])).
% 4.58/1.86  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.58/1.86  tff(c_964, plain, (![A_80, B_81, C_82]: (k5_xboole_0(k5_xboole_0(A_80, B_81), C_82)=k5_xboole_0(A_80, k5_xboole_0(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.58/1.86  tff(c_4435, plain, (![A_159, B_160, C_161]: (k5_xboole_0(k5_xboole_0(A_159, B_160), C_161)=k5_xboole_0(B_160, k5_xboole_0(A_159, C_161)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_964])).
% 4.58/1.86  tff(c_34, plain, (![A_31, B_32]: (k5_xboole_0(k5_xboole_0(A_31, B_32), k3_xboole_0(A_31, B_32))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.58/1.86  tff(c_4531, plain, (![B_160, A_159]: (k5_xboole_0(B_160, k5_xboole_0(A_159, k3_xboole_0(A_159, B_160)))=k2_xboole_0(A_159, B_160))), inference(superposition, [status(thm), theory('equality')], [c_4435, c_34])).
% 4.58/1.86  tff(c_4859, plain, (![B_164, A_165]: (k5_xboole_0(B_164, k4_xboole_0(A_165, B_164))=k2_xboole_0(A_165, B_164))), inference(demodulation, [status(thm), theory('equality')], [c_3202, c_4531])).
% 4.58/1.86  tff(c_4956, plain, (![B_72, A_71]: (k5_xboole_0(k2_xboole_0(B_72, A_71), k1_xboole_0)=k2_xboole_0(A_71, k2_xboole_0(B_72, A_71)))), inference(superposition, [status(thm), theory('equality')], [c_772, c_4859])).
% 4.58/1.86  tff(c_5000, plain, (![B_72, A_71]: (k2_xboole_0(B_72, A_71)=k2_xboole_0(A_71, B_72))), inference(demodulation, [status(thm), theory('equality')], [c_429, c_24, c_4956])).
% 4.58/1.86  tff(c_4661, plain, (![B_160, A_159]: (k5_xboole_0(B_160, k4_xboole_0(A_159, B_160))=k2_xboole_0(A_159, B_160))), inference(demodulation, [status(thm), theory('equality')], [c_3202, c_4531])).
% 4.58/1.86  tff(c_36, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.58/1.86  tff(c_4858, plain, (k2_xboole_0('#skF_2', '#skF_1')!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4661, c_36])).
% 4.58/1.86  tff(c_5209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5000, c_4858])).
% 4.58/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.58/1.86  
% 4.58/1.86  Inference rules
% 4.58/1.86  ----------------------
% 4.58/1.86  #Ref     : 0
% 4.58/1.86  #Sup     : 1306
% 4.58/1.86  #Fact    : 0
% 4.58/1.86  #Define  : 0
% 4.58/1.86  #Split   : 0
% 4.58/1.86  #Chain   : 0
% 4.58/1.86  #Close   : 0
% 4.58/1.86  
% 4.58/1.86  Ordering : KBO
% 4.58/1.86  
% 4.58/1.86  Simplification rules
% 4.58/1.86  ----------------------
% 4.58/1.86  #Subsume      : 23
% 4.58/1.86  #Demod        : 1163
% 4.58/1.86  #Tautology    : 835
% 4.58/1.86  #SimpNegUnit  : 0
% 4.58/1.86  #BackRed      : 6
% 4.58/1.86  
% 4.58/1.86  #Partial instantiations: 0
% 4.58/1.86  #Strategies tried      : 1
% 4.58/1.86  
% 4.58/1.86  Timing (in seconds)
% 4.58/1.86  ----------------------
% 4.58/1.86  Preprocessing        : 0.28
% 4.58/1.86  Parsing              : 0.15
% 4.58/1.86  CNF conversion       : 0.02
% 4.58/1.86  Main loop            : 0.82
% 4.58/1.86  Inferencing          : 0.25
% 4.58/1.86  Reduction            : 0.38
% 4.58/1.86  Demodulation         : 0.32
% 4.58/1.86  BG Simplification    : 0.03
% 4.58/1.86  Subsumption          : 0.11
% 4.58/1.86  Abstraction          : 0.04
% 4.58/1.86  MUC search           : 0.00
% 4.58/1.86  Cooper               : 0.00
% 4.58/1.86  Total                : 1.13
% 4.58/1.86  Index Insertion      : 0.00
% 4.58/1.86  Index Deletion       : 0.00
% 4.58/1.86  Index Matching       : 0.00
% 4.58/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
