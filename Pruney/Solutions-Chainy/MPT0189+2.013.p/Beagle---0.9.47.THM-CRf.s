%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:52 EST 2020

% Result     : Theorem 12.00s
% Output     : CNFRefutation 12.00s
% Verified   : 
% Statistics : Number of formulae       :   49 (  71 expanded)
%              Number of leaves         :   28 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   30 (  52 expanded)
%              Number of equality atoms :   29 (  51 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_12,plain,(
    ! [A_19,C_21,B_20,D_22] : k2_enumset1(A_19,C_21,B_20,D_22) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_15,B_16,D_18,C_17] : k2_enumset1(A_15,B_16,D_18,C_17) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [A_55,B_56,C_57,D_58] : k3_enumset1(A_55,A_55,B_56,C_57,D_58) = k2_enumset1(A_55,B_56,C_57,D_58) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_50,B_51] : k1_enumset1(A_50,A_50,B_51) = k2_tarski(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [D_62,A_59,C_61,E_63,B_60] : k4_enumset1(A_59,A_59,B_60,C_61,D_62,E_63) = k3_enumset1(A_59,B_60,C_61,D_62,E_63) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_52,B_53,C_54] : k2_enumset1(A_52,A_52,B_53,C_54) = k1_enumset1(A_52,B_53,C_54) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_651,plain,(
    ! [B_137,A_138,C_134,E_136,D_135,F_133] : k2_xboole_0(k2_enumset1(A_138,B_137,C_134,D_135),k2_tarski(E_136,F_133)) = k4_enumset1(A_138,B_137,C_134,D_135,E_136,F_133) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_690,plain,(
    ! [B_53,A_52,E_136,F_133,C_54] : k4_enumset1(A_52,A_52,B_53,C_54,E_136,F_133) = k2_xboole_0(k1_enumset1(A_52,B_53,C_54),k2_tarski(E_136,F_133)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_651])).

tff(c_2334,plain,(
    ! [A_202,B_203,F_201,C_205,E_204] : k2_xboole_0(k1_enumset1(A_202,B_203,C_205),k2_tarski(E_204,F_201)) = k3_enumset1(A_202,B_203,C_205,E_204,F_201) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_690])).

tff(c_2361,plain,(
    ! [A_50,B_51,E_204,F_201] : k3_enumset1(A_50,A_50,B_51,E_204,F_201) = k2_xboole_0(k2_tarski(A_50,B_51),k2_tarski(E_204,F_201)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2334])).

tff(c_2373,plain,(
    ! [A_50,B_51,E_204,F_201] : k2_xboole_0(k2_tarski(A_50,B_51),k2_tarski(E_204,F_201)) = k2_enumset1(A_50,B_51,E_204,F_201) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2361])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18489,plain,(
    ! [A_483,B_482,C_480,E_481,F_484] : k2_xboole_0(k2_tarski(E_481,F_484),k1_enumset1(A_483,B_482,C_480)) = k3_enumset1(A_483,B_482,C_480,E_481,F_484) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2334])).

tff(c_18528,plain,(
    ! [A_50,B_51,E_481,F_484] : k3_enumset1(A_50,A_50,B_51,E_481,F_484) = k2_xboole_0(k2_tarski(E_481,F_484),k2_tarski(A_50,B_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_18489])).

tff(c_18546,plain,(
    ! [E_481,F_484,A_50,B_51] : k2_enumset1(E_481,F_484,A_50,B_51) = k2_enumset1(A_50,B_51,E_481,F_484) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2373,c_28,c_18528])).

tff(c_36,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_37,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_36])).

tff(c_38,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_4','#skF_3') != k2_enumset1('#skF_1','#skF_3','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_37])).

tff(c_39,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_38])).

tff(c_24799,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18546,c_39])).

tff(c_24802,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_24799])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:34:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.00/4.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.00/4.95  
% 12.00/4.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.00/4.95  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.00/4.95  
% 12.00/4.95  %Foreground sorts:
% 12.00/4.95  
% 12.00/4.95  
% 12.00/4.95  %Background operators:
% 12.00/4.95  
% 12.00/4.95  
% 12.00/4.95  %Foreground operators:
% 12.00/4.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.00/4.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.00/4.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.00/4.95  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.00/4.95  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.00/4.95  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.00/4.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.00/4.95  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.00/4.95  tff('#skF_2', type, '#skF_2': $i).
% 12.00/4.95  tff('#skF_3', type, '#skF_3': $i).
% 12.00/4.95  tff('#skF_1', type, '#skF_1': $i).
% 12.00/4.95  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.00/4.95  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.00/4.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.00/4.95  tff('#skF_4', type, '#skF_4': $i).
% 12.00/4.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.00/4.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.00/4.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.00/4.95  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.00/4.95  
% 12.00/4.96  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 12.00/4.96  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 12.00/4.96  tff(f_53, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 12.00/4.96  tff(f_49, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 12.00/4.96  tff(f_55, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 12.00/4.96  tff(f_51, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 12.00/4.96  tff(f_41, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 12.00/4.96  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.00/4.96  tff(f_62, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 12.00/4.96  tff(c_12, plain, (![A_19, C_21, B_20, D_22]: (k2_enumset1(A_19, C_21, B_20, D_22)=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.00/4.96  tff(c_10, plain, (![A_15, B_16, D_18, C_17]: (k2_enumset1(A_15, B_16, D_18, C_17)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.00/4.96  tff(c_28, plain, (![A_55, B_56, C_57, D_58]: (k3_enumset1(A_55, A_55, B_56, C_57, D_58)=k2_enumset1(A_55, B_56, C_57, D_58))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.00/4.96  tff(c_24, plain, (![A_50, B_51]: (k1_enumset1(A_50, A_50, B_51)=k2_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.00/4.96  tff(c_30, plain, (![D_62, A_59, C_61, E_63, B_60]: (k4_enumset1(A_59, A_59, B_60, C_61, D_62, E_63)=k3_enumset1(A_59, B_60, C_61, D_62, E_63))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.00/4.96  tff(c_26, plain, (![A_52, B_53, C_54]: (k2_enumset1(A_52, A_52, B_53, C_54)=k1_enumset1(A_52, B_53, C_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.00/4.96  tff(c_651, plain, (![B_137, A_138, C_134, E_136, D_135, F_133]: (k2_xboole_0(k2_enumset1(A_138, B_137, C_134, D_135), k2_tarski(E_136, F_133))=k4_enumset1(A_138, B_137, C_134, D_135, E_136, F_133))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.00/4.96  tff(c_690, plain, (![B_53, A_52, E_136, F_133, C_54]: (k4_enumset1(A_52, A_52, B_53, C_54, E_136, F_133)=k2_xboole_0(k1_enumset1(A_52, B_53, C_54), k2_tarski(E_136, F_133)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_651])).
% 12.00/4.96  tff(c_2334, plain, (![A_202, B_203, F_201, C_205, E_204]: (k2_xboole_0(k1_enumset1(A_202, B_203, C_205), k2_tarski(E_204, F_201))=k3_enumset1(A_202, B_203, C_205, E_204, F_201))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_690])).
% 12.00/4.96  tff(c_2361, plain, (![A_50, B_51, E_204, F_201]: (k3_enumset1(A_50, A_50, B_51, E_204, F_201)=k2_xboole_0(k2_tarski(A_50, B_51), k2_tarski(E_204, F_201)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2334])).
% 12.00/4.96  tff(c_2373, plain, (![A_50, B_51, E_204, F_201]: (k2_xboole_0(k2_tarski(A_50, B_51), k2_tarski(E_204, F_201))=k2_enumset1(A_50, B_51, E_204, F_201))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2361])).
% 12.00/4.96  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.00/4.96  tff(c_18489, plain, (![A_483, B_482, C_480, E_481, F_484]: (k2_xboole_0(k2_tarski(E_481, F_484), k1_enumset1(A_483, B_482, C_480))=k3_enumset1(A_483, B_482, C_480, E_481, F_484))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2334])).
% 12.00/4.96  tff(c_18528, plain, (![A_50, B_51, E_481, F_484]: (k3_enumset1(A_50, A_50, B_51, E_481, F_484)=k2_xboole_0(k2_tarski(E_481, F_484), k2_tarski(A_50, B_51)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_18489])).
% 12.00/4.96  tff(c_18546, plain, (![E_481, F_484, A_50, B_51]: (k2_enumset1(E_481, F_484, A_50, B_51)=k2_enumset1(A_50, B_51, E_481, F_484))), inference(demodulation, [status(thm), theory('equality')], [c_2373, c_28, c_18528])).
% 12.00/4.96  tff(c_36, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.00/4.96  tff(c_37, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_36])).
% 12.00/4.96  tff(c_38, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_4', '#skF_3')!=k2_enumset1('#skF_1', '#skF_3', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_37])).
% 12.00/4.96  tff(c_39, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_38])).
% 12.00/4.96  tff(c_24799, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18546, c_39])).
% 12.00/4.96  tff(c_24802, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_24799])).
% 12.00/4.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.00/4.96  
% 12.00/4.96  Inference rules
% 12.00/4.96  ----------------------
% 12.00/4.96  #Ref     : 0
% 12.00/4.96  #Sup     : 6163
% 12.00/4.96  #Fact    : 0
% 12.00/4.96  #Define  : 0
% 12.00/4.96  #Split   : 0
% 12.00/4.96  #Chain   : 0
% 12.00/4.96  #Close   : 0
% 12.00/4.96  
% 12.00/4.96  Ordering : KBO
% 12.00/4.96  
% 12.00/4.96  Simplification rules
% 12.00/4.96  ----------------------
% 12.00/4.96  #Subsume      : 1260
% 12.00/4.96  #Demod        : 5325
% 12.00/4.96  #Tautology    : 2868
% 12.00/4.96  #SimpNegUnit  : 0
% 12.00/4.96  #BackRed      : 34
% 12.00/4.96  
% 12.00/4.96  #Partial instantiations: 0
% 12.00/4.96  #Strategies tried      : 1
% 12.00/4.96  
% 12.00/4.96  Timing (in seconds)
% 12.00/4.96  ----------------------
% 12.00/4.96  Preprocessing        : 0.33
% 12.00/4.96  Parsing              : 0.17
% 12.00/4.96  CNF conversion       : 0.02
% 12.00/4.96  Main loop            : 3.89
% 12.00/4.96  Inferencing          : 0.92
% 12.00/4.96  Reduction            : 2.24
% 12.00/4.96  Demodulation         : 2.06
% 12.00/4.96  BG Simplification    : 0.14
% 12.00/4.96  Subsumption          : 0.42
% 12.00/4.96  Abstraction          : 0.19
% 12.00/4.96  MUC search           : 0.00
% 12.00/4.96  Cooper               : 0.00
% 12.00/4.96  Total                : 4.24
% 12.00/4.97  Index Insertion      : 0.00
% 12.00/4.97  Index Deletion       : 0.00
% 12.00/4.97  Index Matching       : 0.00
% 12.00/4.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
