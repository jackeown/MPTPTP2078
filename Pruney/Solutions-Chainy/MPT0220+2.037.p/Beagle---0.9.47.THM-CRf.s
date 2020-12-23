%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:08 EST 2020

% Result     : Theorem 7.62s
% Output     : CNFRefutation 7.78s
% Verified   : 
% Statistics : Number of formulae       :   55 (  86 expanded)
%              Number of leaves         :   28 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   38 (  69 expanded)
%              Number of equality atoms :   33 (  64 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_16,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    ! [A_46,B_47] : r1_tarski(k1_tarski(A_46),k2_tarski(A_46,B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_199,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(A_63,B_64) = k1_xboole_0
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1063,plain,(
    ! [A_105,B_106] : k4_xboole_0(k1_tarski(A_105),k2_tarski(A_105,B_106)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_199])).

tff(c_20,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1071,plain,(
    ! [A_105,B_106] : k2_xboole_0(k2_tarski(A_105,B_106),k1_tarski(A_105)) = k5_xboole_0(k2_tarski(A_105,B_106),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1063,c_20])).

tff(c_9186,plain,(
    ! [A_240,B_241] : k2_xboole_0(k2_tarski(A_240,B_241),k1_tarski(A_240)) = k2_tarski(A_240,B_241) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1071])).

tff(c_69,plain,(
    ! [B_54,A_55] : k5_xboole_0(B_54,A_55) = k5_xboole_0(A_55,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_85,plain,(
    ! [A_55] : k5_xboole_0(k1_xboole_0,A_55) = A_55 ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_16])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_584,plain,(
    ! [A_85,B_86,C_87] : k5_xboole_0(k5_xboole_0(A_85,B_86),C_87) = k5_xboole_0(A_85,k5_xboole_0(B_86,C_87)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2275,plain,(
    ! [B_153,A_154,B_155] : k5_xboole_0(B_153,k5_xboole_0(A_154,B_155)) = k5_xboole_0(A_154,k5_xboole_0(B_155,B_153)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_584])).

tff(c_2676,plain,(
    ! [A_156,B_157] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_156,B_157)) = k5_xboole_0(B_157,A_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_2275])).

tff(c_2796,plain,(
    ! [B_17,A_16] : k5_xboole_0(k4_xboole_0(B_17,A_16),A_16) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2676])).

tff(c_2843,plain,(
    ! [B_17,A_16] : k5_xboole_0(k4_xboole_0(B_17,A_16),A_16) = k2_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_2796])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_370,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_392,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_370])).

tff(c_2764,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_2676])).

tff(c_2834,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k4_xboole_0(B_2,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_2764])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5542,plain,(
    ! [A_198,B_199,C_200] : k5_xboole_0(A_198,k5_xboole_0(k3_xboole_0(A_198,B_199),C_200)) = k5_xboole_0(k4_xboole_0(A_198,B_199),C_200) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_584])).

tff(c_5633,plain,(
    ! [A_1,B_2] : k5_xboole_0(k4_xboole_0(A_1,B_2),B_2) = k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2834,c_5542])).

tff(c_5759,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2843,c_20,c_5633])).

tff(c_9216,plain,(
    ! [A_240,B_241] : k2_xboole_0(k1_tarski(A_240),k2_tarski(A_240,B_241)) = k2_tarski(A_240,B_241) ),
    inference(superposition,[status(thm),theory(equality)],[c_9186,c_5759])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12762,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9216,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:41:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.62/3.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.62/3.07  
% 7.62/3.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.62/3.07  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 7.62/3.07  
% 7.62/3.07  %Foreground sorts:
% 7.62/3.07  
% 7.62/3.07  
% 7.62/3.07  %Background operators:
% 7.62/3.07  
% 7.62/3.07  
% 7.62/3.07  %Foreground operators:
% 7.62/3.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.62/3.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.62/3.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.62/3.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.62/3.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.62/3.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.62/3.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.62/3.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.62/3.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.62/3.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.62/3.07  tff('#skF_2', type, '#skF_2': $i).
% 7.62/3.07  tff('#skF_1', type, '#skF_1': $i).
% 7.62/3.07  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.62/3.07  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.62/3.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.62/3.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.62/3.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.62/3.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.62/3.07  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.62/3.07  
% 7.78/3.08  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 7.78/3.08  tff(f_61, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 7.78/3.08  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.78/3.08  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.78/3.08  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.78/3.08  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.78/3.08  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.78/3.08  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.78/3.08  tff(f_64, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 7.78/3.08  tff(c_16, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.78/3.08  tff(c_36, plain, (![A_46, B_47]: (r1_tarski(k1_tarski(A_46), k2_tarski(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.78/3.08  tff(c_199, plain, (![A_63, B_64]: (k4_xboole_0(A_63, B_64)=k1_xboole_0 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.78/3.08  tff(c_1063, plain, (![A_105, B_106]: (k4_xboole_0(k1_tarski(A_105), k2_tarski(A_105, B_106))=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_199])).
% 7.78/3.08  tff(c_20, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.78/3.08  tff(c_1071, plain, (![A_105, B_106]: (k2_xboole_0(k2_tarski(A_105, B_106), k1_tarski(A_105))=k5_xboole_0(k2_tarski(A_105, B_106), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1063, c_20])).
% 7.78/3.08  tff(c_9186, plain, (![A_240, B_241]: (k2_xboole_0(k2_tarski(A_240, B_241), k1_tarski(A_240))=k2_tarski(A_240, B_241))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1071])).
% 7.78/3.08  tff(c_69, plain, (![B_54, A_55]: (k5_xboole_0(B_54, A_55)=k5_xboole_0(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.78/3.08  tff(c_85, plain, (![A_55]: (k5_xboole_0(k1_xboole_0, A_55)=A_55)), inference(superposition, [status(thm), theory('equality')], [c_69, c_16])).
% 7.78/3.08  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.78/3.08  tff(c_584, plain, (![A_85, B_86, C_87]: (k5_xboole_0(k5_xboole_0(A_85, B_86), C_87)=k5_xboole_0(A_85, k5_xboole_0(B_86, C_87)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.78/3.08  tff(c_2275, plain, (![B_153, A_154, B_155]: (k5_xboole_0(B_153, k5_xboole_0(A_154, B_155))=k5_xboole_0(A_154, k5_xboole_0(B_155, B_153)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_584])).
% 7.78/3.08  tff(c_2676, plain, (![A_156, B_157]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_156, B_157))=k5_xboole_0(B_157, A_156))), inference(superposition, [status(thm), theory('equality')], [c_85, c_2275])).
% 7.78/3.08  tff(c_2796, plain, (![B_17, A_16]: (k5_xboole_0(k4_xboole_0(B_17, A_16), A_16)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2676])).
% 7.78/3.08  tff(c_2843, plain, (![B_17, A_16]: (k5_xboole_0(k4_xboole_0(B_17, A_16), A_16)=k2_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_2796])).
% 7.78/3.08  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.78/3.08  tff(c_370, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.78/3.08  tff(c_392, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_370])).
% 7.78/3.08  tff(c_2764, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k5_xboole_0(k1_xboole_0, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_392, c_2676])).
% 7.78/3.08  tff(c_2834, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k4_xboole_0(B_2, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_2764])).
% 7.78/3.08  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.78/3.08  tff(c_5542, plain, (![A_198, B_199, C_200]: (k5_xboole_0(A_198, k5_xboole_0(k3_xboole_0(A_198, B_199), C_200))=k5_xboole_0(k4_xboole_0(A_198, B_199), C_200))), inference(superposition, [status(thm), theory('equality')], [c_10, c_584])).
% 7.78/3.08  tff(c_5633, plain, (![A_1, B_2]: (k5_xboole_0(k4_xboole_0(A_1, B_2), B_2)=k5_xboole_0(A_1, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2834, c_5542])).
% 7.78/3.08  tff(c_5759, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_2843, c_20, c_5633])).
% 7.78/3.08  tff(c_9216, plain, (![A_240, B_241]: (k2_xboole_0(k1_tarski(A_240), k2_tarski(A_240, B_241))=k2_tarski(A_240, B_241))), inference(superposition, [status(thm), theory('equality')], [c_9186, c_5759])).
% 7.78/3.08  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.78/3.08  tff(c_12762, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9216, c_38])).
% 7.78/3.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.78/3.08  
% 7.78/3.08  Inference rules
% 7.78/3.08  ----------------------
% 7.78/3.08  #Ref     : 0
% 7.78/3.08  #Sup     : 3174
% 7.78/3.08  #Fact    : 0
% 7.78/3.08  #Define  : 0
% 7.78/3.08  #Split   : 0
% 7.78/3.08  #Chain   : 0
% 7.78/3.08  #Close   : 0
% 7.78/3.08  
% 7.78/3.08  Ordering : KBO
% 7.78/3.08  
% 7.78/3.08  Simplification rules
% 7.78/3.08  ----------------------
% 7.78/3.08  #Subsume      : 200
% 7.78/3.08  #Demod        : 3611
% 7.78/3.08  #Tautology    : 1831
% 7.78/3.08  #SimpNegUnit  : 0
% 7.78/3.08  #BackRed      : 2
% 7.78/3.08  
% 7.78/3.08  #Partial instantiations: 0
% 7.78/3.08  #Strategies tried      : 1
% 7.78/3.08  
% 7.78/3.08  Timing (in seconds)
% 7.78/3.08  ----------------------
% 7.78/3.09  Preprocessing        : 0.30
% 7.78/3.09  Parsing              : 0.16
% 7.78/3.09  CNF conversion       : 0.02
% 7.78/3.09  Main loop            : 2.00
% 7.78/3.09  Inferencing          : 0.46
% 7.78/3.09  Reduction            : 1.16
% 7.78/3.09  Demodulation         : 1.05
% 7.78/3.09  BG Simplification    : 0.06
% 7.78/3.09  Subsumption          : 0.24
% 7.78/3.09  Abstraction          : 0.10
% 7.78/3.09  MUC search           : 0.00
% 7.78/3.09  Cooper               : 0.00
% 7.78/3.09  Total                : 2.33
% 7.78/3.09  Index Insertion      : 0.00
% 7.78/3.09  Index Deletion       : 0.00
% 7.78/3.09  Index Matching       : 0.00
% 7.78/3.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
