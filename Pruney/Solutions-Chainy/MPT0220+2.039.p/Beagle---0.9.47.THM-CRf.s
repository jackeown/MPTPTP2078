%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:09 EST 2020

% Result     : Theorem 7.79s
% Output     : CNFRefutation 7.79s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 215 expanded)
%              Number of leaves         :   30 (  86 expanded)
%              Depth                    :   15
%              Number of atoms          :   60 ( 208 expanded)
%              Number of equality atoms :   53 ( 183 expanded)
%              Maximal formula depth    :   10 (   3 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_284,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k4_xboole_0(B_69,A_68)) = k2_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_94,plain,(
    ! [B_56,A_57] : k5_xboole_0(B_56,A_57) = k5_xboole_0(A_57,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_110,plain,(
    ! [A_57] : k5_xboole_0(k1_xboole_0,A_57) = A_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_14])).

tff(c_291,plain,(
    ! [B_69] : k4_xboole_0(B_69,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_110])).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_181,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(A_59,B_60) = A_59
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_194,plain,(
    ! [A_61] : k3_xboole_0(k1_xboole_0,A_61) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_181])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_199,plain,(
    ! [A_61] : k3_xboole_0(A_61,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_2])).

tff(c_337,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k4_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_353,plain,(
    ! [A_61] : k5_xboole_0(A_61,k1_xboole_0) = k4_xboole_0(A_61,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_337])).

tff(c_370,plain,(
    ! [A_61] : k2_xboole_0(k1_xboole_0,A_61) = A_61 ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_14,c_353])).

tff(c_304,plain,(
    ! [B_70] : k4_xboole_0(B_70,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_110])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_313,plain,(
    ! [B_70] : k4_xboole_0(B_70,k2_xboole_0(k1_xboole_0,B_70)) = k3_xboole_0(B_70,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_12])).

tff(c_319,plain,(
    ! [B_70] : k4_xboole_0(B_70,k2_xboole_0(k1_xboole_0,B_70)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_313])).

tff(c_448,plain,(
    ! [B_70] : k4_xboole_0(B_70,B_70) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_319])).

tff(c_449,plain,(
    ! [B_69] : k4_xboole_0(B_69,k1_xboole_0) = B_69 ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_291])).

tff(c_548,plain,(
    ! [B_83] : k4_xboole_0(B_83,B_83) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_319])).

tff(c_559,plain,(
    ! [B_83] : k4_xboole_0(B_83,k1_xboole_0) = k3_xboole_0(B_83,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_12])).

tff(c_647,plain,(
    ! [B_90] : k3_xboole_0(B_90,B_90) = B_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_559])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_653,plain,(
    ! [B_90] : k5_xboole_0(B_90,B_90) = k4_xboole_0(B_90,B_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_6])).

tff(c_674,plain,(
    ! [B_90] : k5_xboole_0(B_90,B_90) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_653])).

tff(c_34,plain,(
    ! [A_46,B_47] : r1_tarski(k1_tarski(A_46),k2_tarski(A_46,B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1190,plain,(
    ! [A_120,B_121] : k3_xboole_0(k1_tarski(A_120),k2_tarski(A_120,B_121)) = k1_tarski(A_120) ),
    inference(resolution,[status(thm)],[c_34,c_181])).

tff(c_1199,plain,(
    ! [A_120,B_121] : k5_xboole_0(k1_tarski(A_120),k1_tarski(A_120)) = k4_xboole_0(k1_tarski(A_120),k2_tarski(A_120,B_121)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1190,c_6])).

tff(c_1210,plain,(
    ! [A_122,B_123] : k4_xboole_0(k1_tarski(A_122),k2_tarski(A_122,B_123)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_1199])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1215,plain,(
    ! [A_122,B_123] : k2_xboole_0(k2_tarski(A_122,B_123),k1_tarski(A_122)) = k5_xboole_0(k2_tarski(A_122,B_123),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1210,c_18])).

tff(c_12726,plain,(
    ! [A_259,B_260] : k2_xboole_0(k2_tarski(A_259,B_260),k1_tarski(A_259)) = k2_tarski(A_259,B_260) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1215])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_471,plain,(
    ! [A_80,B_81,C_82] : k5_xboole_0(k5_xboole_0(A_80,B_81),C_82) = k5_xboole_0(A_80,k5_xboole_0(B_81,C_82)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1440,plain,(
    ! [B_130,A_131,B_132] : k5_xboole_0(B_130,k5_xboole_0(A_131,B_132)) = k5_xboole_0(A_131,k5_xboole_0(B_132,B_130)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_471])).

tff(c_1796,plain,(
    ! [A_133,B_134] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_133,B_134)) = k5_xboole_0(B_134,A_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_1440])).

tff(c_1904,plain,(
    ! [B_17,A_16] : k5_xboole_0(k4_xboole_0(B_17,A_16),A_16) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1796])).

tff(c_1948,plain,(
    ! [B_17,A_16] : k5_xboole_0(k4_xboole_0(B_17,A_16),A_16) = k2_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_1904])).

tff(c_366,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_337])).

tff(c_1872,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_1796])).

tff(c_1939,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k4_xboole_0(B_2,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_1872])).

tff(c_5949,plain,(
    ! [A_203,B_204,C_205] : k5_xboole_0(A_203,k5_xboole_0(k3_xboole_0(A_203,B_204),C_205)) = k5_xboole_0(k4_xboole_0(A_203,B_204),C_205) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_471])).

tff(c_6061,plain,(
    ! [A_1,B_2] : k5_xboole_0(k4_xboole_0(A_1,B_2),B_2) = k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1939,c_5949])).

tff(c_6176,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1948,c_18,c_6061])).

tff(c_12753,plain,(
    ! [A_259,B_260] : k2_xboole_0(k1_tarski(A_259),k2_tarski(A_259,B_260)) = k2_tarski(A_259,B_260) ),
    inference(superposition,[status(thm),theory(equality)],[c_12726,c_6176])).

tff(c_36,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12753,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:41:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.79/3.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.79/3.12  
% 7.79/3.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.79/3.12  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 7.79/3.12  
% 7.79/3.12  %Foreground sorts:
% 7.79/3.12  
% 7.79/3.12  
% 7.79/3.12  %Background operators:
% 7.79/3.12  
% 7.79/3.12  
% 7.79/3.12  %Foreground operators:
% 7.79/3.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.79/3.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.79/3.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.79/3.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.79/3.12  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.79/3.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.79/3.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.79/3.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.79/3.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.79/3.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.79/3.12  tff('#skF_2', type, '#skF_2': $i).
% 7.79/3.12  tff('#skF_1', type, '#skF_1': $i).
% 7.79/3.12  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.79/3.12  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.79/3.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.79/3.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.79/3.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.79/3.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.79/3.12  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.79/3.12  
% 7.79/3.14  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 7.79/3.14  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.79/3.14  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.79/3.14  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.79/3.14  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.79/3.14  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.79/3.14  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.79/3.14  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.79/3.14  tff(f_61, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 7.79/3.14  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.79/3.14  tff(f_64, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 7.79/3.14  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.79/3.14  tff(c_284, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k4_xboole_0(B_69, A_68))=k2_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.79/3.14  tff(c_94, plain, (![B_56, A_57]: (k5_xboole_0(B_56, A_57)=k5_xboole_0(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.79/3.14  tff(c_110, plain, (![A_57]: (k5_xboole_0(k1_xboole_0, A_57)=A_57)), inference(superposition, [status(thm), theory('equality')], [c_94, c_14])).
% 7.79/3.14  tff(c_291, plain, (![B_69]: (k4_xboole_0(B_69, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_69))), inference(superposition, [status(thm), theory('equality')], [c_284, c_110])).
% 7.79/3.14  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.79/3.14  tff(c_181, plain, (![A_59, B_60]: (k3_xboole_0(A_59, B_60)=A_59 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.79/3.14  tff(c_194, plain, (![A_61]: (k3_xboole_0(k1_xboole_0, A_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_181])).
% 7.79/3.14  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.79/3.14  tff(c_199, plain, (![A_61]: (k3_xboole_0(A_61, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_194, c_2])).
% 7.79/3.14  tff(c_337, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k4_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.79/3.14  tff(c_353, plain, (![A_61]: (k5_xboole_0(A_61, k1_xboole_0)=k4_xboole_0(A_61, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_199, c_337])).
% 7.79/3.14  tff(c_370, plain, (![A_61]: (k2_xboole_0(k1_xboole_0, A_61)=A_61)), inference(demodulation, [status(thm), theory('equality')], [c_291, c_14, c_353])).
% 7.79/3.14  tff(c_304, plain, (![B_70]: (k4_xboole_0(B_70, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_70))), inference(superposition, [status(thm), theory('equality')], [c_284, c_110])).
% 7.79/3.14  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.79/3.14  tff(c_313, plain, (![B_70]: (k4_xboole_0(B_70, k2_xboole_0(k1_xboole_0, B_70))=k3_xboole_0(B_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_304, c_12])).
% 7.79/3.14  tff(c_319, plain, (![B_70]: (k4_xboole_0(B_70, k2_xboole_0(k1_xboole_0, B_70))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_199, c_313])).
% 7.79/3.14  tff(c_448, plain, (![B_70]: (k4_xboole_0(B_70, B_70)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_370, c_319])).
% 7.79/3.14  tff(c_449, plain, (![B_69]: (k4_xboole_0(B_69, k1_xboole_0)=B_69)), inference(demodulation, [status(thm), theory('equality')], [c_370, c_291])).
% 7.79/3.14  tff(c_548, plain, (![B_83]: (k4_xboole_0(B_83, B_83)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_370, c_319])).
% 7.79/3.14  tff(c_559, plain, (![B_83]: (k4_xboole_0(B_83, k1_xboole_0)=k3_xboole_0(B_83, B_83))), inference(superposition, [status(thm), theory('equality')], [c_548, c_12])).
% 7.79/3.14  tff(c_647, plain, (![B_90]: (k3_xboole_0(B_90, B_90)=B_90)), inference(demodulation, [status(thm), theory('equality')], [c_449, c_559])).
% 7.79/3.14  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.79/3.14  tff(c_653, plain, (![B_90]: (k5_xboole_0(B_90, B_90)=k4_xboole_0(B_90, B_90))), inference(superposition, [status(thm), theory('equality')], [c_647, c_6])).
% 7.79/3.14  tff(c_674, plain, (![B_90]: (k5_xboole_0(B_90, B_90)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_448, c_653])).
% 7.79/3.14  tff(c_34, plain, (![A_46, B_47]: (r1_tarski(k1_tarski(A_46), k2_tarski(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.79/3.14  tff(c_1190, plain, (![A_120, B_121]: (k3_xboole_0(k1_tarski(A_120), k2_tarski(A_120, B_121))=k1_tarski(A_120))), inference(resolution, [status(thm)], [c_34, c_181])).
% 7.79/3.14  tff(c_1199, plain, (![A_120, B_121]: (k5_xboole_0(k1_tarski(A_120), k1_tarski(A_120))=k4_xboole_0(k1_tarski(A_120), k2_tarski(A_120, B_121)))), inference(superposition, [status(thm), theory('equality')], [c_1190, c_6])).
% 7.79/3.14  tff(c_1210, plain, (![A_122, B_123]: (k4_xboole_0(k1_tarski(A_122), k2_tarski(A_122, B_123))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_674, c_1199])).
% 7.79/3.14  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.79/3.14  tff(c_1215, plain, (![A_122, B_123]: (k2_xboole_0(k2_tarski(A_122, B_123), k1_tarski(A_122))=k5_xboole_0(k2_tarski(A_122, B_123), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1210, c_18])).
% 7.79/3.14  tff(c_12726, plain, (![A_259, B_260]: (k2_xboole_0(k2_tarski(A_259, B_260), k1_tarski(A_259))=k2_tarski(A_259, B_260))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1215])).
% 7.79/3.14  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.79/3.14  tff(c_471, plain, (![A_80, B_81, C_82]: (k5_xboole_0(k5_xboole_0(A_80, B_81), C_82)=k5_xboole_0(A_80, k5_xboole_0(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.79/3.14  tff(c_1440, plain, (![B_130, A_131, B_132]: (k5_xboole_0(B_130, k5_xboole_0(A_131, B_132))=k5_xboole_0(A_131, k5_xboole_0(B_132, B_130)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_471])).
% 7.79/3.14  tff(c_1796, plain, (![A_133, B_134]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_133, B_134))=k5_xboole_0(B_134, A_133))), inference(superposition, [status(thm), theory('equality')], [c_110, c_1440])).
% 7.79/3.14  tff(c_1904, plain, (![B_17, A_16]: (k5_xboole_0(k4_xboole_0(B_17, A_16), A_16)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1796])).
% 7.79/3.14  tff(c_1948, plain, (![B_17, A_16]: (k5_xboole_0(k4_xboole_0(B_17, A_16), A_16)=k2_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_1904])).
% 7.79/3.14  tff(c_366, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_337])).
% 7.79/3.14  tff(c_1872, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k5_xboole_0(k1_xboole_0, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_366, c_1796])).
% 7.79/3.14  tff(c_1939, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k4_xboole_0(B_2, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_1872])).
% 7.79/3.14  tff(c_5949, plain, (![A_203, B_204, C_205]: (k5_xboole_0(A_203, k5_xboole_0(k3_xboole_0(A_203, B_204), C_205))=k5_xboole_0(k4_xboole_0(A_203, B_204), C_205))), inference(superposition, [status(thm), theory('equality')], [c_6, c_471])).
% 7.79/3.14  tff(c_6061, plain, (![A_1, B_2]: (k5_xboole_0(k4_xboole_0(A_1, B_2), B_2)=k5_xboole_0(A_1, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_1939, c_5949])).
% 7.79/3.14  tff(c_6176, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_1948, c_18, c_6061])).
% 7.79/3.14  tff(c_12753, plain, (![A_259, B_260]: (k2_xboole_0(k1_tarski(A_259), k2_tarski(A_259, B_260))=k2_tarski(A_259, B_260))), inference(superposition, [status(thm), theory('equality')], [c_12726, c_6176])).
% 7.79/3.14  tff(c_36, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.79/3.14  tff(c_12796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12753, c_36])).
% 7.79/3.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.79/3.14  
% 7.79/3.14  Inference rules
% 7.79/3.14  ----------------------
% 7.79/3.14  #Ref     : 0
% 7.79/3.14  #Sup     : 3183
% 7.79/3.14  #Fact    : 0
% 7.79/3.14  #Define  : 0
% 7.79/3.14  #Split   : 0
% 7.79/3.14  #Chain   : 0
% 7.79/3.14  #Close   : 0
% 7.79/3.14  
% 7.79/3.14  Ordering : KBO
% 7.79/3.14  
% 7.79/3.14  Simplification rules
% 7.79/3.14  ----------------------
% 7.79/3.14  #Subsume      : 181
% 7.79/3.14  #Demod        : 3619
% 7.79/3.14  #Tautology    : 1855
% 7.79/3.14  #SimpNegUnit  : 0
% 7.79/3.14  #BackRed      : 3
% 7.79/3.14  
% 7.79/3.14  #Partial instantiations: 0
% 7.79/3.14  #Strategies tried      : 1
% 7.79/3.14  
% 7.79/3.14  Timing (in seconds)
% 7.79/3.14  ----------------------
% 7.79/3.14  Preprocessing        : 0.30
% 7.79/3.14  Parsing              : 0.16
% 7.79/3.14  CNF conversion       : 0.02
% 7.79/3.14  Main loop            : 2.08
% 7.79/3.14  Inferencing          : 0.45
% 7.79/3.14  Reduction            : 1.25
% 7.79/3.14  Demodulation         : 1.13
% 7.79/3.14  BG Simplification    : 0.06
% 7.79/3.14  Subsumption          : 0.23
% 7.79/3.14  Abstraction          : 0.10
% 7.79/3.14  MUC search           : 0.00
% 7.79/3.14  Cooper               : 0.00
% 7.79/3.14  Total                : 2.41
% 7.79/3.14  Index Insertion      : 0.00
% 7.79/3.14  Index Deletion       : 0.00
% 7.79/3.14  Index Matching       : 0.00
% 7.79/3.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
