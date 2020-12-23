%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:40 EST 2020

% Result     : Theorem 34.23s
% Output     : CNFRefutation 34.29s
% Verified   : 
% Statistics : Number of formulae       :   48 (  74 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  63 expanded)
%              Number of equality atoms :   36 (  62 expanded)
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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(c_173,plain,(
    ! [B_58,A_59] : k2_xboole_0(B_58,A_59) = k2_xboole_0(A_59,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_201,plain,(
    ! [A_59] : k2_xboole_0(k1_xboole_0,A_59) = A_59 ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_8])).

tff(c_438,plain,(
    ! [A_67,B_68] : k2_xboole_0(A_67,k4_xboole_0(B_68,A_67)) = k2_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_448,plain,(
    ! [B_68] : k4_xboole_0(B_68,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_201])).

tff(c_478,plain,(
    ! [B_68] : k4_xboole_0(B_68,k1_xboole_0) = B_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_448])).

tff(c_62,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k2_xboole_0(A_48,B_49)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_72,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_62])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    ! [A_33,B_34] : k4_xboole_0(k2_xboole_0(A_33,B_34),k3_xboole_0(A_33,B_34)) = k2_xboole_0(k4_xboole_0(A_33,B_34),k4_xboole_0(B_34,A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    ! [A_33,B_34] : k4_xboole_0(k2_xboole_0(A_33,B_34),k3_xboole_0(A_33,B_34)) = k5_xboole_0(A_33,B_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_32])).

tff(c_2437,plain,(
    ! [A_119,B_120] : k2_xboole_0(k5_xboole_0(A_119,B_120),k3_xboole_0(A_119,B_120)) = k2_xboole_0(A_119,B_120) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(k2_xboole_0(A_16,B_17),B_17) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2467,plain,(
    ! [A_119,B_120] : k4_xboole_0(k5_xboole_0(A_119,B_120),k3_xboole_0(A_119,B_120)) = k4_xboole_0(k2_xboole_0(A_119,B_120),k3_xboole_0(A_119,B_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2437,c_18])).

tff(c_11290,plain,(
    ! [A_252,B_253] : k4_xboole_0(k5_xboole_0(A_252,B_253),k3_xboole_0(A_252,B_253)) = k5_xboole_0(A_252,B_253) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2467])).

tff(c_26,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_11398,plain,(
    ! [A_252,B_253] : k4_xboole_0(k5_xboole_0(A_252,B_253),k5_xboole_0(A_252,B_253)) = k3_xboole_0(k5_xboole_0(A_252,B_253),k3_xboole_0(A_252,B_253)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11290,c_26])).

tff(c_11505,plain,(
    ! [A_252,B_253] : k3_xboole_0(k5_xboole_0(A_252,B_253),k3_xboole_0(A_252,B_253)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_11398])).

tff(c_2640,plain,(
    ! [A_125,B_126] : k2_xboole_0(k4_xboole_0(A_125,B_126),k4_xboole_0(B_126,A_125)) = k5_xboole_0(A_125,B_126) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10172,plain,(
    ! [B_242,A_243] : k2_xboole_0(k4_xboole_0(B_242,A_243),k4_xboole_0(A_243,B_242)) = k5_xboole_0(A_243,B_242) ),
    inference(superposition,[status(thm),theory(equality)],[c_2640,c_2])).

tff(c_10245,plain,(
    ! [B_242,A_243] : k5_xboole_0(B_242,A_243) = k5_xboole_0(A_243,B_242) ),
    inference(superposition,[status(thm),theory(equality)],[c_10172,c_4])).

tff(c_2443,plain,(
    ! [A_119,B_120] : k4_xboole_0(k2_xboole_0(A_119,B_120),k3_xboole_0(k5_xboole_0(A_119,B_120),k3_xboole_0(A_119,B_120))) = k5_xboole_0(k5_xboole_0(A_119,B_120),k3_xboole_0(A_119,B_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2437,c_44])).

tff(c_136662,plain,(
    ! [A_119,B_120] : k5_xboole_0(k3_xboole_0(A_119,B_120),k5_xboole_0(A_119,B_120)) = k2_xboole_0(A_119,B_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_11505,c_10245,c_2443])).

tff(c_42,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10539,plain,(
    k5_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10245,c_42])).

tff(c_136665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136662,c_10539])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:44:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 34.23/25.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 34.23/25.65  
% 34.23/25.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 34.23/25.65  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 34.23/25.65  
% 34.23/25.65  %Foreground sorts:
% 34.23/25.65  
% 34.23/25.65  
% 34.23/25.65  %Background operators:
% 34.23/25.65  
% 34.23/25.65  
% 34.23/25.65  %Foreground operators:
% 34.23/25.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 34.23/25.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 34.23/25.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 34.23/25.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 34.23/25.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 34.23/25.65  tff('#skF_2', type, '#skF_2': $i).
% 34.23/25.65  tff('#skF_1', type, '#skF_1': $i).
% 34.23/25.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 34.23/25.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 34.23/25.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 34.23/25.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 34.23/25.65  
% 34.29/25.66  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 34.29/25.66  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 34.29/25.66  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 34.29/25.66  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 34.29/25.66  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 34.29/25.66  tff(f_57, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_xboole_1)).
% 34.29/25.66  tff(f_71, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 34.29/25.66  tff(f_43, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 34.29/25.66  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 34.29/25.66  tff(f_74, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 34.29/25.66  tff(c_173, plain, (![B_58, A_59]: (k2_xboole_0(B_58, A_59)=k2_xboole_0(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_27])).
% 34.29/25.66  tff(c_8, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_33])).
% 34.29/25.66  tff(c_201, plain, (![A_59]: (k2_xboole_0(k1_xboole_0, A_59)=A_59)), inference(superposition, [status(thm), theory('equality')], [c_173, c_8])).
% 34.29/25.66  tff(c_438, plain, (![A_67, B_68]: (k2_xboole_0(A_67, k4_xboole_0(B_68, A_67))=k2_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_41])).
% 34.29/25.66  tff(c_448, plain, (![B_68]: (k4_xboole_0(B_68, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_68))), inference(superposition, [status(thm), theory('equality')], [c_438, c_201])).
% 34.29/25.66  tff(c_478, plain, (![B_68]: (k4_xboole_0(B_68, k1_xboole_0)=B_68)), inference(demodulation, [status(thm), theory('equality')], [c_201, c_448])).
% 34.29/25.66  tff(c_62, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k2_xboole_0(A_48, B_49))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 34.29/25.66  tff(c_72, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_62])).
% 34.29/25.66  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 34.29/25.66  tff(c_32, plain, (![A_33, B_34]: (k4_xboole_0(k2_xboole_0(A_33, B_34), k3_xboole_0(A_33, B_34))=k2_xboole_0(k4_xboole_0(A_33, B_34), k4_xboole_0(B_34, A_33)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 34.29/25.66  tff(c_44, plain, (![A_33, B_34]: (k4_xboole_0(k2_xboole_0(A_33, B_34), k3_xboole_0(A_33, B_34))=k5_xboole_0(A_33, B_34))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_32])).
% 34.29/25.66  tff(c_2437, plain, (![A_119, B_120]: (k2_xboole_0(k5_xboole_0(A_119, B_120), k3_xboole_0(A_119, B_120))=k2_xboole_0(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_71])).
% 34.29/25.66  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(k2_xboole_0(A_16, B_17), B_17)=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 34.29/25.66  tff(c_2467, plain, (![A_119, B_120]: (k4_xboole_0(k5_xboole_0(A_119, B_120), k3_xboole_0(A_119, B_120))=k4_xboole_0(k2_xboole_0(A_119, B_120), k3_xboole_0(A_119, B_120)))), inference(superposition, [status(thm), theory('equality')], [c_2437, c_18])).
% 34.29/25.66  tff(c_11290, plain, (![A_252, B_253]: (k4_xboole_0(k5_xboole_0(A_252, B_253), k3_xboole_0(A_252, B_253))=k5_xboole_0(A_252, B_253))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2467])).
% 34.29/25.66  tff(c_26, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_51])).
% 34.29/25.66  tff(c_11398, plain, (![A_252, B_253]: (k4_xboole_0(k5_xboole_0(A_252, B_253), k5_xboole_0(A_252, B_253))=k3_xboole_0(k5_xboole_0(A_252, B_253), k3_xboole_0(A_252, B_253)))), inference(superposition, [status(thm), theory('equality')], [c_11290, c_26])).
% 34.29/25.66  tff(c_11505, plain, (![A_252, B_253]: (k3_xboole_0(k5_xboole_0(A_252, B_253), k3_xboole_0(A_252, B_253))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_11398])).
% 34.29/25.66  tff(c_2640, plain, (![A_125, B_126]: (k2_xboole_0(k4_xboole_0(A_125, B_126), k4_xboole_0(B_126, A_125))=k5_xboole_0(A_125, B_126))), inference(cnfTransformation, [status(thm)], [f_29])).
% 34.29/25.66  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 34.29/25.66  tff(c_10172, plain, (![B_242, A_243]: (k2_xboole_0(k4_xboole_0(B_242, A_243), k4_xboole_0(A_243, B_242))=k5_xboole_0(A_243, B_242))), inference(superposition, [status(thm), theory('equality')], [c_2640, c_2])).
% 34.29/25.66  tff(c_10245, plain, (![B_242, A_243]: (k5_xboole_0(B_242, A_243)=k5_xboole_0(A_243, B_242))), inference(superposition, [status(thm), theory('equality')], [c_10172, c_4])).
% 34.29/25.66  tff(c_2443, plain, (![A_119, B_120]: (k4_xboole_0(k2_xboole_0(A_119, B_120), k3_xboole_0(k5_xboole_0(A_119, B_120), k3_xboole_0(A_119, B_120)))=k5_xboole_0(k5_xboole_0(A_119, B_120), k3_xboole_0(A_119, B_120)))), inference(superposition, [status(thm), theory('equality')], [c_2437, c_44])).
% 34.29/25.66  tff(c_136662, plain, (![A_119, B_120]: (k5_xboole_0(k3_xboole_0(A_119, B_120), k5_xboole_0(A_119, B_120))=k2_xboole_0(A_119, B_120))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_11505, c_10245, c_2443])).
% 34.29/25.66  tff(c_42, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 34.29/25.66  tff(c_10539, plain, (k5_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10245, c_42])).
% 34.29/25.66  tff(c_136665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136662, c_10539])).
% 34.29/25.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 34.29/25.66  
% 34.29/25.66  Inference rules
% 34.29/25.66  ----------------------
% 34.29/25.66  #Ref     : 0
% 34.29/25.66  #Sup     : 34626
% 34.29/25.66  #Fact    : 0
% 34.29/25.66  #Define  : 0
% 34.29/25.66  #Split   : 2
% 34.29/25.66  #Chain   : 0
% 34.29/25.66  #Close   : 0
% 34.29/25.66  
% 34.29/25.66  Ordering : KBO
% 34.29/25.66  
% 34.29/25.66  Simplification rules
% 34.29/25.66  ----------------------
% 34.29/25.66  #Subsume      : 768
% 34.29/25.66  #Demod        : 48980
% 34.29/25.66  #Tautology    : 19326
% 34.29/25.66  #SimpNegUnit  : 0
% 34.29/25.66  #BackRed      : 11
% 34.29/25.66  
% 34.29/25.66  #Partial instantiations: 0
% 34.29/25.66  #Strategies tried      : 1
% 34.29/25.66  
% 34.29/25.66  Timing (in seconds)
% 34.29/25.66  ----------------------
% 34.29/25.67  Preprocessing        : 0.39
% 34.29/25.67  Parsing              : 0.20
% 34.29/25.67  CNF conversion       : 0.03
% 34.29/25.67  Main loop            : 24.50
% 34.29/25.67  Inferencing          : 2.25
% 34.29/25.67  Reduction            : 17.27
% 34.29/25.67  Demodulation         : 16.23
% 34.29/25.67  BG Simplification    : 0.37
% 34.29/25.67  Subsumption          : 3.77
% 34.29/25.67  Abstraction          : 0.76
% 34.29/25.67  MUC search           : 0.00
% 34.29/25.67  Cooper               : 0.00
% 34.29/25.67  Total                : 24.92
% 34.29/25.67  Index Insertion      : 0.00
% 34.29/25.67  Index Deletion       : 0.00
% 34.29/25.67  Index Matching       : 0.00
% 34.29/25.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
