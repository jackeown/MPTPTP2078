%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:07 EST 2020

% Result     : Theorem 53.41s
% Output     : CNFRefutation 53.41s
% Verified   : 
% Statistics : Number of formulae       :   55 (  85 expanded)
%              Number of leaves         :   25 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  73 expanded)
%              Number of equality atoms :   42 (  72 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(f_38,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_72,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_48,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_80,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(A,k5_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,k2_xboole_0(B,C)),k3_xboole_0(k3_xboole_0(A,B),C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_xboole_1)).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(k2_xboole_0(A_12,B_13),k3_xboole_0(A_12,B_13)) = k5_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3335,plain,(
    ! [A_151,B_152,C_153] : k2_xboole_0(k4_xboole_0(A_151,B_152),k3_xboole_0(A_151,C_153)) = k4_xboole_0(A_151,k4_xboole_0(B_152,C_153)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3366,plain,(
    ! [A_151,C_153,B_152] : k2_xboole_0(k3_xboole_0(A_151,C_153),k4_xboole_0(A_151,B_152)) = k4_xboole_0(A_151,k4_xboole_0(B_152,C_153)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3335,c_2])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_226,plain,(
    ! [B_72,A_73] : k5_xboole_0(B_72,A_73) = k5_xboole_0(A_73,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_51] : k5_xboole_0(A_51,k1_xboole_0) = A_51 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_242,plain,(
    ! [A_73] : k5_xboole_0(k1_xboole_0,A_73) = A_73 ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_48])).

tff(c_24,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_359,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k4_xboole_0(B_80,A_79)) = k2_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_382,plain,(
    ! [A_22] : k5_xboole_0(k1_xboole_0,A_22) = k2_xboole_0(k1_xboole_0,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_359])).

tff(c_389,plain,(
    ! [A_22] : k2_xboole_0(k1_xboole_0,A_22) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_382])).

tff(c_32,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k2_xboole_0(A_31,B_32)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3430,plain,(
    ! [A_31,B_32,C_153] : k4_xboole_0(A_31,k4_xboole_0(k2_xboole_0(A_31,B_32),C_153)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_31,C_153)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3335])).

tff(c_3473,plain,(
    ! [A_31,B_32,C_153] : k4_xboole_0(A_31,k4_xboole_0(k2_xboole_0(A_31,B_32),C_153)) = k3_xboole_0(A_31,C_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_3430])).

tff(c_3730,plain,(
    ! [A_158,B_159,C_160] : k4_xboole_0(k3_xboole_0(A_158,B_159),k3_xboole_0(A_158,C_160)) = k3_xboole_0(A_158,k4_xboole_0(B_159,C_160)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    ! [A_37,B_38,C_39] : k4_xboole_0(k3_xboole_0(A_37,B_38),C_39) = k3_xboole_0(A_37,k4_xboole_0(B_38,C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3757,plain,(
    ! [A_158,B_159,C_160] : k3_xboole_0(A_158,k4_xboole_0(B_159,k3_xboole_0(A_158,C_160))) = k3_xboole_0(A_158,k4_xboole_0(B_159,C_160)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3730,c_38])).

tff(c_6043,plain,(
    ! [A_189,B_190,C_191] : k2_xboole_0(k3_xboole_0(A_189,B_190),k3_xboole_0(A_189,C_191)) = k3_xboole_0(A_189,k2_xboole_0(B_190,C_191)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6097,plain,(
    ! [A_189,B_190,C_191] : k4_xboole_0(k3_xboole_0(A_189,B_190),k3_xboole_0(A_189,k2_xboole_0(B_190,C_191))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6043,c_32])).

tff(c_88887,plain,(
    ! [A_618,B_619,B_620] : k2_xboole_0(k4_xboole_0(A_618,B_619),k3_xboole_0(B_620,A_618)) = k4_xboole_0(A_618,k4_xboole_0(B_619,B_620)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3335])).

tff(c_89250,plain,(
    ! [A_189,B_190,C_191,B_620] : k4_xboole_0(k3_xboole_0(A_189,B_190),k4_xboole_0(k3_xboole_0(A_189,k2_xboole_0(B_190,C_191)),B_620)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(B_620,k3_xboole_0(A_189,B_190))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6097,c_88887])).

tff(c_89646,plain,(
    ! [B_620,A_189,B_190] : k3_xboole_0(B_620,k3_xboole_0(A_189,B_190)) = k3_xboole_0(A_189,k3_xboole_0(B_190,B_620)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3473,c_3757,c_38,c_38,c_389,c_89250])).

tff(c_6,plain,(
    ! [B_6,A_5] : k5_xboole_0(B_6,A_5) = k5_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_3')) != k4_xboole_0('#skF_1',k5_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_61,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_3')) != k4_xboole_0('#skF_1',k5_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_60])).

tff(c_62,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k3_xboole_0('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) != k4_xboole_0('#skF_1',k5_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_61])).

tff(c_63,plain,(
    k2_xboole_0(k3_xboole_0('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) != k4_xboole_0('#skF_1',k5_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_62])).

tff(c_198766,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) != k4_xboole_0('#skF_1',k5_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89646,c_63])).

tff(c_198769,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3366,c_4,c_198766])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:32:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 53.41/44.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 53.41/44.97  
% 53.41/44.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 53.41/44.98  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 53.41/44.98  
% 53.41/44.98  %Foreground sorts:
% 53.41/44.98  
% 53.41/44.98  
% 53.41/44.98  %Background operators:
% 53.41/44.98  
% 53.41/44.98  
% 53.41/44.98  %Foreground operators:
% 53.41/44.98  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 53.41/44.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 53.41/44.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 53.41/44.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 53.41/44.98  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 53.41/44.98  tff('#skF_2', type, '#skF_2': $i).
% 53.41/44.98  tff('#skF_3', type, '#skF_3': $i).
% 53.41/44.98  tff('#skF_1', type, '#skF_1': $i).
% 53.41/44.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 53.41/44.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 53.41/44.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 53.41/44.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 53.41/44.98  
% 53.41/44.99  tff(f_38, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 53.41/44.99  tff(f_68, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 53.41/44.99  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 53.41/44.99  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 53.41/44.99  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 53.41/44.99  tff(f_72, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 53.41/44.99  tff(f_48, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 53.41/44.99  tff(f_80, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 53.41/44.99  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 53.41/44.99  tff(f_64, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_xboole_1)).
% 53.41/44.99  tff(f_62, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 53.41/44.99  tff(f_42, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 53.41/44.99  tff(f_85, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(A, k5_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, k2_xboole_0(B, C)), k3_xboole_0(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_xboole_1)).
% 53.41/44.99  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(k2_xboole_0(A_12, B_13), k3_xboole_0(A_12, B_13))=k5_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_38])).
% 53.41/44.99  tff(c_3335, plain, (![A_151, B_152, C_153]: (k2_xboole_0(k4_xboole_0(A_151, B_152), k3_xboole_0(A_151, C_153))=k4_xboole_0(A_151, k4_xboole_0(B_152, C_153)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 53.41/44.99  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 53.41/44.99  tff(c_3366, plain, (![A_151, C_153, B_152]: (k2_xboole_0(k3_xboole_0(A_151, C_153), k4_xboole_0(A_151, B_152))=k4_xboole_0(A_151, k4_xboole_0(B_152, C_153)))), inference(superposition, [status(thm), theory('equality')], [c_3335, c_2])).
% 53.41/44.99  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 53.41/44.99  tff(c_226, plain, (![B_72, A_73]: (k5_xboole_0(B_72, A_73)=k5_xboole_0(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_31])).
% 53.41/44.99  tff(c_48, plain, (![A_51]: (k5_xboole_0(A_51, k1_xboole_0)=A_51)), inference(cnfTransformation, [status(thm)], [f_72])).
% 53.41/44.99  tff(c_242, plain, (![A_73]: (k5_xboole_0(k1_xboole_0, A_73)=A_73)), inference(superposition, [status(thm), theory('equality')], [c_226, c_48])).
% 53.41/44.99  tff(c_24, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_48])).
% 53.41/44.99  tff(c_359, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k4_xboole_0(B_80, A_79))=k2_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_80])).
% 53.41/44.99  tff(c_382, plain, (![A_22]: (k5_xboole_0(k1_xboole_0, A_22)=k2_xboole_0(k1_xboole_0, A_22))), inference(superposition, [status(thm), theory('equality')], [c_24, c_359])).
% 53.41/44.99  tff(c_389, plain, (![A_22]: (k2_xboole_0(k1_xboole_0, A_22)=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_242, c_382])).
% 53.41/44.99  tff(c_32, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k2_xboole_0(A_31, B_32))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 53.41/44.99  tff(c_3430, plain, (![A_31, B_32, C_153]: (k4_xboole_0(A_31, k4_xboole_0(k2_xboole_0(A_31, B_32), C_153))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_31, C_153)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_3335])).
% 53.41/44.99  tff(c_3473, plain, (![A_31, B_32, C_153]: (k4_xboole_0(A_31, k4_xboole_0(k2_xboole_0(A_31, B_32), C_153))=k3_xboole_0(A_31, C_153))), inference(demodulation, [status(thm), theory('equality')], [c_389, c_3430])).
% 53.41/44.99  tff(c_3730, plain, (![A_158, B_159, C_160]: (k4_xboole_0(k3_xboole_0(A_158, B_159), k3_xboole_0(A_158, C_160))=k3_xboole_0(A_158, k4_xboole_0(B_159, C_160)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 53.41/44.99  tff(c_38, plain, (![A_37, B_38, C_39]: (k4_xboole_0(k3_xboole_0(A_37, B_38), C_39)=k3_xboole_0(A_37, k4_xboole_0(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 53.41/44.99  tff(c_3757, plain, (![A_158, B_159, C_160]: (k3_xboole_0(A_158, k4_xboole_0(B_159, k3_xboole_0(A_158, C_160)))=k3_xboole_0(A_158, k4_xboole_0(B_159, C_160)))), inference(superposition, [status(thm), theory('equality')], [c_3730, c_38])).
% 53.41/44.99  tff(c_6043, plain, (![A_189, B_190, C_191]: (k2_xboole_0(k3_xboole_0(A_189, B_190), k3_xboole_0(A_189, C_191))=k3_xboole_0(A_189, k2_xboole_0(B_190, C_191)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 53.41/44.99  tff(c_6097, plain, (![A_189, B_190, C_191]: (k4_xboole_0(k3_xboole_0(A_189, B_190), k3_xboole_0(A_189, k2_xboole_0(B_190, C_191)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6043, c_32])).
% 53.41/44.99  tff(c_88887, plain, (![A_618, B_619, B_620]: (k2_xboole_0(k4_xboole_0(A_618, B_619), k3_xboole_0(B_620, A_618))=k4_xboole_0(A_618, k4_xboole_0(B_619, B_620)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_3335])).
% 53.41/44.99  tff(c_89250, plain, (![A_189, B_190, C_191, B_620]: (k4_xboole_0(k3_xboole_0(A_189, B_190), k4_xboole_0(k3_xboole_0(A_189, k2_xboole_0(B_190, C_191)), B_620))=k2_xboole_0(k1_xboole_0, k3_xboole_0(B_620, k3_xboole_0(A_189, B_190))))), inference(superposition, [status(thm), theory('equality')], [c_6097, c_88887])).
% 53.41/44.99  tff(c_89646, plain, (![B_620, A_189, B_190]: (k3_xboole_0(B_620, k3_xboole_0(A_189, B_190))=k3_xboole_0(A_189, k3_xboole_0(B_190, B_620)))), inference(demodulation, [status(thm), theory('equality')], [c_3473, c_3757, c_38, c_38, c_389, c_89250])).
% 53.41/44.99  tff(c_6, plain, (![B_6, A_5]: (k5_xboole_0(B_6, A_5)=k5_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 53.41/44.99  tff(c_60, plain, (k2_xboole_0(k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_3'))!=k4_xboole_0('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 53.41/44.99  tff(c_61, plain, (k2_xboole_0(k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_3'))!=k4_xboole_0('#skF_1', k5_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_60])).
% 53.41/44.99  tff(c_62, plain, (k2_xboole_0(k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k3_xboole_0('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))!=k4_xboole_0('#skF_1', k5_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_61])).
% 53.41/44.99  tff(c_63, plain, (k2_xboole_0(k3_xboole_0('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))!=k4_xboole_0('#skF_1', k5_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_62])).
% 53.41/44.99  tff(c_198766, plain, (k2_xboole_0(k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))!=k4_xboole_0('#skF_1', k5_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_89646, c_63])).
% 53.41/44.99  tff(c_198769, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_3366, c_4, c_198766])).
% 53.41/44.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 53.41/44.99  
% 53.41/44.99  Inference rules
% 53.41/44.99  ----------------------
% 53.41/44.99  #Ref     : 0
% 53.41/44.99  #Sup     : 50978
% 53.41/44.99  #Fact    : 0
% 53.41/44.99  #Define  : 0
% 53.41/44.99  #Split   : 0
% 53.41/44.99  #Chain   : 0
% 53.41/44.99  #Close   : 0
% 53.41/44.99  
% 53.41/44.99  Ordering : KBO
% 53.41/44.99  
% 53.41/44.99  Simplification rules
% 53.41/44.99  ----------------------
% 53.41/44.99  #Subsume      : 834
% 53.41/44.99  #Demod        : 73997
% 53.41/44.99  #Tautology    : 25519
% 53.41/44.99  #SimpNegUnit  : 0
% 53.41/44.99  #BackRed      : 36
% 53.41/44.99  
% 53.41/44.99  #Partial instantiations: 0
% 53.41/44.99  #Strategies tried      : 1
% 53.41/44.99  
% 53.41/44.99  Timing (in seconds)
% 53.41/44.99  ----------------------
% 53.41/44.99  Preprocessing        : 0.33
% 53.41/44.99  Parsing              : 0.17
% 53.41/44.99  CNF conversion       : 0.02
% 53.41/44.99  Main loop            : 43.90
% 53.41/44.99  Inferencing          : 3.37
% 53.41/44.99  Reduction            : 31.26
% 53.41/44.99  Demodulation         : 29.80
% 53.41/44.99  BG Simplification    : 0.58
% 53.41/44.99  Subsumption          : 7.22
% 53.41/44.99  Abstraction          : 1.20
% 53.41/44.99  MUC search           : 0.00
% 53.41/44.99  Cooper               : 0.00
% 53.41/44.99  Total                : 44.26
% 53.41/44.99  Index Insertion      : 0.00
% 53.41/44.99  Index Deletion       : 0.00
% 53.41/44.99  Index Matching       : 0.00
% 53.41/44.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
