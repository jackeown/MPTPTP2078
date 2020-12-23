%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:55 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   44 (  50 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  40 expanded)
%              Number of equality atoms :   33 (  39 expanded)
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

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_226,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_229,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k3_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,k4_xboole_0(A_30,B_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_8])).

tff(c_248,plain,(
    ! [A_30,B_31] : k3_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k4_xboole_0(A_30,B_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_229])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_47,plain,(
    ! [B_20,A_21] : k5_xboole_0(B_20,A_21) = k5_xboole_0(A_21,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_63,plain,(
    ! [A_21] : k5_xboole_0(k1_xboole_0,A_21) = A_21 ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_10])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_287,plain,(
    ! [A_34,B_35,C_36] : k5_xboole_0(k5_xboole_0(A_34,B_35),C_36) = k5_xboole_0(A_34,k5_xboole_0(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_351,plain,(
    ! [A_13,C_36] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_36)) = k5_xboole_0(k1_xboole_0,C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_287])).

tff(c_365,plain,(
    ! [A_37,C_38] : k5_xboole_0(A_37,k5_xboole_0(A_37,C_38)) = C_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_351])).

tff(c_398,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k4_xboole_0(B_17,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_365])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1800,plain,(
    ! [A_66,B_67,C_68] : k5_xboole_0(k5_xboole_0(A_66,B_67),C_68) = k5_xboole_0(B_67,k5_xboole_0(A_66,C_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_287])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(k5_xboole_0(A_14,B_15),k2_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1860,plain,(
    ! [B_67,A_66] : k5_xboole_0(B_67,k5_xboole_0(A_66,k2_xboole_0(A_66,B_67))) = k3_xboole_0(A_66,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_1800,c_16])).

tff(c_2086,plain,(
    ! [B_70,A_71] : k5_xboole_0(B_70,k4_xboole_0(B_70,A_71)) = k3_xboole_0(A_71,B_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_1860])).

tff(c_2158,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k3_xboole_0(k4_xboole_0(A_7,B_8),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2086])).

tff(c_2182,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_2,c_2158])).

tff(c_20,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2182,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:14:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.64  
% 3.62/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.65  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.62/1.65  
% 3.62/1.65  %Foreground sorts:
% 3.62/1.65  
% 3.62/1.65  
% 3.62/1.65  %Background operators:
% 3.62/1.65  
% 3.62/1.65  
% 3.62/1.65  %Foreground operators:
% 3.62/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.62/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.62/1.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.62/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.62/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.62/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.62/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.62/1.65  
% 3.62/1.66  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.62/1.66  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.62/1.66  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.62/1.66  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.62/1.66  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.62/1.66  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.62/1.66  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.62/1.66  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.62/1.66  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.62/1.66  tff(f_46, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.62/1.66  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.62/1.66  tff(c_226, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.62/1.66  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.62/1.66  tff(c_229, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k3_xboole_0(A_30, B_31))=k3_xboole_0(A_30, k4_xboole_0(A_30, B_31)))), inference(superposition, [status(thm), theory('equality')], [c_226, c_8])).
% 3.62/1.66  tff(c_248, plain, (![A_30, B_31]: (k3_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k4_xboole_0(A_30, B_31))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_229])).
% 3.62/1.66  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.62/1.66  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.62/1.66  tff(c_47, plain, (![B_20, A_21]: (k5_xboole_0(B_20, A_21)=k5_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.62/1.66  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.62/1.66  tff(c_63, plain, (![A_21]: (k5_xboole_0(k1_xboole_0, A_21)=A_21)), inference(superposition, [status(thm), theory('equality')], [c_47, c_10])).
% 3.62/1.66  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.62/1.66  tff(c_287, plain, (![A_34, B_35, C_36]: (k5_xboole_0(k5_xboole_0(A_34, B_35), C_36)=k5_xboole_0(A_34, k5_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.62/1.66  tff(c_351, plain, (![A_13, C_36]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_36))=k5_xboole_0(k1_xboole_0, C_36))), inference(superposition, [status(thm), theory('equality')], [c_14, c_287])).
% 3.62/1.66  tff(c_365, plain, (![A_37, C_38]: (k5_xboole_0(A_37, k5_xboole_0(A_37, C_38))=C_38)), inference(demodulation, [status(thm), theory('equality')], [c_63, c_351])).
% 3.62/1.66  tff(c_398, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k4_xboole_0(B_17, A_16))), inference(superposition, [status(thm), theory('equality')], [c_18, c_365])).
% 3.62/1.66  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.62/1.66  tff(c_1800, plain, (![A_66, B_67, C_68]: (k5_xboole_0(k5_xboole_0(A_66, B_67), C_68)=k5_xboole_0(B_67, k5_xboole_0(A_66, C_68)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_287])).
% 3.62/1.66  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(k5_xboole_0(A_14, B_15), k2_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.62/1.66  tff(c_1860, plain, (![B_67, A_66]: (k5_xboole_0(B_67, k5_xboole_0(A_66, k2_xboole_0(A_66, B_67)))=k3_xboole_0(A_66, B_67))), inference(superposition, [status(thm), theory('equality')], [c_1800, c_16])).
% 3.62/1.66  tff(c_2086, plain, (![B_70, A_71]: (k5_xboole_0(B_70, k4_xboole_0(B_70, A_71))=k3_xboole_0(A_71, B_70))), inference(demodulation, [status(thm), theory('equality')], [c_398, c_1860])).
% 3.62/1.66  tff(c_2158, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k3_xboole_0(k4_xboole_0(A_7, B_8), A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2086])).
% 3.62/1.66  tff(c_2182, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(demodulation, [status(thm), theory('equality')], [c_248, c_2, c_2158])).
% 3.62/1.66  tff(c_20, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.62/1.66  tff(c_2264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2182, c_20])).
% 3.62/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.66  
% 3.62/1.66  Inference rules
% 3.62/1.66  ----------------------
% 3.62/1.66  #Ref     : 0
% 3.62/1.66  #Sup     : 566
% 3.62/1.66  #Fact    : 0
% 3.62/1.66  #Define  : 0
% 3.62/1.66  #Split   : 0
% 3.62/1.66  #Chain   : 0
% 3.62/1.66  #Close   : 0
% 3.62/1.66  
% 3.62/1.66  Ordering : KBO
% 3.62/1.66  
% 3.62/1.66  Simplification rules
% 3.62/1.66  ----------------------
% 3.62/1.66  #Subsume      : 25
% 3.62/1.66  #Demod        : 368
% 3.62/1.66  #Tautology    : 272
% 3.62/1.66  #SimpNegUnit  : 0
% 3.62/1.66  #BackRed      : 1
% 3.62/1.66  
% 3.62/1.66  #Partial instantiations: 0
% 3.62/1.66  #Strategies tried      : 1
% 3.62/1.66  
% 3.62/1.66  Timing (in seconds)
% 3.62/1.66  ----------------------
% 3.62/1.66  Preprocessing        : 0.32
% 3.62/1.66  Parsing              : 0.16
% 3.62/1.66  CNF conversion       : 0.02
% 3.62/1.66  Main loop            : 0.56
% 3.62/1.66  Inferencing          : 0.18
% 3.62/1.66  Reduction            : 0.26
% 3.62/1.66  Demodulation         : 0.23
% 3.62/1.66  BG Simplification    : 0.03
% 3.62/1.66  Subsumption          : 0.07
% 3.62/1.66  Abstraction          : 0.03
% 3.62/1.66  MUC search           : 0.00
% 3.62/1.66  Cooper               : 0.00
% 3.62/1.66  Total                : 0.90
% 3.62/1.66  Index Insertion      : 0.00
% 3.62/1.66  Index Deletion       : 0.00
% 3.62/1.66  Index Matching       : 0.00
% 3.62/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
