%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:06 EST 2020

% Result     : Theorem 37.04s
% Output     : CNFRefutation 37.10s
% Verified   : 
% Statistics : Number of formulae       :   42 (  55 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   32 (  45 expanded)
%              Number of equality atoms :   31 (  44 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    5 (   3 average)

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_194,plain,(
    ! [A_29,B_30] : k5_xboole_0(A_29,k3_xboole_0(A_29,B_30)) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_220,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_194])).

tff(c_229,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_220])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k3_xboole_0(A_9,B_10),C_11) = k3_xboole_0(A_9,k4_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_214,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_194])).

tff(c_320,plain,(
    ! [A_36,B_37,C_38] : k5_xboole_0(k5_xboole_0(A_36,B_37),C_38) = k5_xboole_0(A_36,k5_xboole_0(B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3546,plain,(
    ! [A_118,B_119,C_120] : k5_xboole_0(A_118,k5_xboole_0(k3_xboole_0(A_118,B_119),C_120)) = k5_xboole_0(k4_xboole_0(A_118,B_119),C_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_320])).

tff(c_3655,plain,(
    ! [A_118,B_119,B_2] : k5_xboole_0(k4_xboole_0(A_118,B_119),k3_xboole_0(B_2,k3_xboole_0(A_118,B_119))) = k5_xboole_0(A_118,k4_xboole_0(k3_xboole_0(A_118,B_119),B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_3546])).

tff(c_3706,plain,(
    ! [A_118,B_119,B_2] : k5_xboole_0(k4_xboole_0(A_118,B_119),k3_xboole_0(B_2,k3_xboole_0(A_118,B_119))) = k4_xboole_0(A_118,k4_xboole_0(B_119,B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_12,c_3655])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4592,plain,(
    ! [A_136,B_137,B_138] : k5_xboole_0(A_136,k5_xboole_0(B_137,k3_xboole_0(k5_xboole_0(A_136,B_137),B_138))) = k4_xboole_0(k5_xboole_0(A_136,B_137),B_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_4])).

tff(c_4784,plain,(
    ! [A_16,B_17,B_138] : k5_xboole_0(A_16,k5_xboole_0(k4_xboole_0(B_17,A_16),k3_xboole_0(k2_xboole_0(A_16,B_17),B_138))) = k4_xboole_0(k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)),B_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4592])).

tff(c_57559,plain,(
    ! [A_491,B_492,B_493] : k5_xboole_0(A_491,k5_xboole_0(k4_xboole_0(B_492,A_491),k3_xboole_0(k2_xboole_0(A_491,B_492),B_493))) = k4_xboole_0(k2_xboole_0(A_491,B_492),B_493) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4784])).

tff(c_57718,plain,(
    ! [B_119,A_118] : k5_xboole_0(B_119,k4_xboole_0(A_118,k4_xboole_0(B_119,k2_xboole_0(B_119,A_118)))) = k4_xboole_0(k2_xboole_0(B_119,A_118),k3_xboole_0(A_118,B_119)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3706,c_57559])).

tff(c_107186,plain,(
    ! [B_682,A_683] : k4_xboole_0(k2_xboole_0(B_682,A_683),k3_xboole_0(A_683,B_682)) = k5_xboole_0(B_682,A_683) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_229,c_57718])).

tff(c_107780,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),k3_xboole_0(B_2,A_1)) = k5_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_107186])).

tff(c_20,plain,(
    k4_xboole_0(k2_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k5_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_117606,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107780,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:29:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 37.04/28.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 37.10/28.31  
% 37.10/28.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 37.10/28.32  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 37.10/28.32  
% 37.10/28.32  %Foreground sorts:
% 37.10/28.32  
% 37.10/28.32  
% 37.10/28.32  %Background operators:
% 37.10/28.32  
% 37.10/28.32  
% 37.10/28.32  %Foreground operators:
% 37.10/28.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 37.10/28.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 37.10/28.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 37.10/28.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 37.10/28.32  tff('#skF_2', type, '#skF_2': $i).
% 37.10/28.32  tff('#skF_1', type, '#skF_1': $i).
% 37.10/28.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 37.10/28.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 37.10/28.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 37.10/28.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 37.10/28.32  
% 37.10/28.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 37.10/28.33  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 37.10/28.33  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 37.10/28.33  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 37.10/28.33  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 37.10/28.33  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 37.10/28.33  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 37.10/28.33  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 37.10/28.33  tff(f_46, negated_conjecture, ~(![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t101_xboole_1)).
% 37.10/28.33  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 37.10/28.33  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 37.10/28.33  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 37.10/28.33  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 37.10/28.33  tff(c_194, plain, (![A_29, B_30]: (k5_xboole_0(A_29, k3_xboole_0(A_29, B_30))=k4_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 37.10/28.33  tff(c_220, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_194])).
% 37.10/28.33  tff(c_229, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_220])).
% 37.10/28.33  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 37.10/28.33  tff(c_12, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k3_xboole_0(A_9, B_10), C_11)=k3_xboole_0(A_9, k4_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 37.10/28.33  tff(c_214, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_194])).
% 37.10/28.33  tff(c_320, plain, (![A_36, B_37, C_38]: (k5_xboole_0(k5_xboole_0(A_36, B_37), C_38)=k5_xboole_0(A_36, k5_xboole_0(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 37.10/28.33  tff(c_3546, plain, (![A_118, B_119, C_120]: (k5_xboole_0(A_118, k5_xboole_0(k3_xboole_0(A_118, B_119), C_120))=k5_xboole_0(k4_xboole_0(A_118, B_119), C_120))), inference(superposition, [status(thm), theory('equality')], [c_4, c_320])).
% 37.10/28.33  tff(c_3655, plain, (![A_118, B_119, B_2]: (k5_xboole_0(k4_xboole_0(A_118, B_119), k3_xboole_0(B_2, k3_xboole_0(A_118, B_119)))=k5_xboole_0(A_118, k4_xboole_0(k3_xboole_0(A_118, B_119), B_2)))), inference(superposition, [status(thm), theory('equality')], [c_214, c_3546])).
% 37.10/28.33  tff(c_3706, plain, (![A_118, B_119, B_2]: (k5_xboole_0(k4_xboole_0(A_118, B_119), k3_xboole_0(B_2, k3_xboole_0(A_118, B_119)))=k4_xboole_0(A_118, k4_xboole_0(B_119, B_2)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_12, c_3655])).
% 37.10/28.33  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 37.10/28.33  tff(c_4592, plain, (![A_136, B_137, B_138]: (k5_xboole_0(A_136, k5_xboole_0(B_137, k3_xboole_0(k5_xboole_0(A_136, B_137), B_138)))=k4_xboole_0(k5_xboole_0(A_136, B_137), B_138))), inference(superposition, [status(thm), theory('equality')], [c_320, c_4])).
% 37.10/28.33  tff(c_4784, plain, (![A_16, B_17, B_138]: (k5_xboole_0(A_16, k5_xboole_0(k4_xboole_0(B_17, A_16), k3_xboole_0(k2_xboole_0(A_16, B_17), B_138)))=k4_xboole_0(k5_xboole_0(A_16, k4_xboole_0(B_17, A_16)), B_138))), inference(superposition, [status(thm), theory('equality')], [c_18, c_4592])).
% 37.10/28.33  tff(c_57559, plain, (![A_491, B_492, B_493]: (k5_xboole_0(A_491, k5_xboole_0(k4_xboole_0(B_492, A_491), k3_xboole_0(k2_xboole_0(A_491, B_492), B_493)))=k4_xboole_0(k2_xboole_0(A_491, B_492), B_493))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4784])).
% 37.10/28.33  tff(c_57718, plain, (![B_119, A_118]: (k5_xboole_0(B_119, k4_xboole_0(A_118, k4_xboole_0(B_119, k2_xboole_0(B_119, A_118))))=k4_xboole_0(k2_xboole_0(B_119, A_118), k3_xboole_0(A_118, B_119)))), inference(superposition, [status(thm), theory('equality')], [c_3706, c_57559])).
% 37.10/28.33  tff(c_107186, plain, (![B_682, A_683]: (k4_xboole_0(k2_xboole_0(B_682, A_683), k3_xboole_0(A_683, B_682))=k5_xboole_0(B_682, A_683))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_229, c_57718])).
% 37.10/28.33  tff(c_107780, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), k3_xboole_0(B_2, A_1))=k5_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_107186])).
% 37.10/28.33  tff(c_20, plain, (k4_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k5_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 37.10/28.33  tff(c_117606, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107780, c_20])).
% 37.10/28.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 37.10/28.33  
% 37.10/28.33  Inference rules
% 37.10/28.33  ----------------------
% 37.10/28.33  #Ref     : 0
% 37.10/28.33  #Sup     : 29320
% 37.10/28.33  #Fact    : 0
% 37.10/28.33  #Define  : 0
% 37.10/28.33  #Split   : 0
% 37.10/28.33  #Chain   : 0
% 37.10/28.33  #Close   : 0
% 37.10/28.33  
% 37.10/28.33  Ordering : KBO
% 37.10/28.33  
% 37.10/28.33  Simplification rules
% 37.10/28.33  ----------------------
% 37.10/28.33  #Subsume      : 370
% 37.10/28.33  #Demod        : 45247
% 37.10/28.33  #Tautology    : 15794
% 37.10/28.33  #SimpNegUnit  : 0
% 37.10/28.33  #BackRed      : 26
% 37.10/28.33  
% 37.10/28.33  #Partial instantiations: 0
% 37.10/28.33  #Strategies tried      : 1
% 37.10/28.33  
% 37.10/28.33  Timing (in seconds)
% 37.10/28.33  ----------------------
% 37.10/28.33  Preprocessing        : 0.27
% 37.10/28.33  Parsing              : 0.14
% 37.10/28.33  CNF conversion       : 0.02
% 37.10/28.33  Main loop            : 27.30
% 37.10/28.33  Inferencing          : 2.83
% 37.10/28.33  Reduction            : 19.57
% 37.10/28.33  Demodulation         : 18.67
% 37.10/28.33  BG Simplification    : 0.47
% 37.10/28.33  Subsumption          : 3.63
% 37.10/28.33  Abstraction          : 0.97
% 37.10/28.33  MUC search           : 0.00
% 37.10/28.33  Cooper               : 0.00
% 37.10/28.33  Total                : 27.60
% 37.10/28.33  Index Insertion      : 0.00
% 37.10/28.33  Index Deletion       : 0.00
% 37.10/28.33  Index Matching       : 0.00
% 37.10/28.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
