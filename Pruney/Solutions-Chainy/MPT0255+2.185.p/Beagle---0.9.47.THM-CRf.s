%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:01 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 136 expanded)
%              Number of leaves         :   34 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :   47 ( 116 expanded)
%              Number of equality atoms :   46 ( 115 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_22,plain,(
    ! [A_22,B_23] : k1_enumset1(A_22,A_22,B_23) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_24,B_25,C_26] : k2_enumset1(A_24,A_24,B_25,C_26) = k1_enumset1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_27,B_28,C_29,D_30] : k3_enumset1(A_27,A_27,B_28,C_29,D_30) = k2_enumset1(A_27,B_28,C_29,D_30) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [A_31,C_33,B_32,E_35,D_34] : k4_enumset1(A_31,A_31,B_32,C_33,D_34,E_35) = k3_enumset1(A_31,B_32,C_33,D_34,E_35) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [B_16,A_15,D_18,E_19,F_20,C_17] : k2_xboole_0(k1_tarski(A_15),k3_enumset1(B_16,C_17,D_18,E_19,F_20)) = k4_enumset1(A_15,B_16,C_17,D_18,E_19,F_20) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_185,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_194,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k4_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_185])).

tff(c_198,plain,(
    ! [A_72] : k4_xboole_0(A_72,k1_xboole_0) = A_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_194])).

tff(c_38,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k2_xboole_0(A_4,B_5)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_6])).

tff(c_207,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_92])).

tff(c_218,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_38])).

tff(c_16,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_204,plain,(
    ! [A_72] : k5_xboole_0(k1_xboole_0,A_72) = k2_xboole_0(k1_xboole_0,A_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_16])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_552,plain,(
    ! [A_89,B_90,C_91] : k5_xboole_0(k5_xboole_0(A_89,B_90),C_91) = k5_xboole_0(A_89,k5_xboole_0(B_90,C_91)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_827,plain,(
    ! [A_105,B_106] : k5_xboole_0(A_105,k5_xboole_0(B_106,k5_xboole_0(A_105,B_106))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_552])).

tff(c_879,plain,(
    ! [A_8] : k5_xboole_0(A_8,k5_xboole_0(k1_xboole_0,A_8)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_827])).

tff(c_895,plain,(
    ! [A_107] : k5_xboole_0(A_107,k2_xboole_0(k1_xboole_0,A_107)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_879])).

tff(c_932,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_895])).

tff(c_941,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_932])).

tff(c_36,plain,(
    ! [A_51,B_52] : k2_xboole_0(k1_tarski(A_51),B_52) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1248,plain,(
    ! [A_129,B_130] : k2_xboole_0(k1_tarski(A_129),B_130) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_941,c_36])).

tff(c_2268,plain,(
    ! [F_163,C_160,D_161,A_165,E_164,B_162] : k4_enumset1(A_165,B_162,C_160,D_161,E_164,F_163) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1248])).

tff(c_2384,plain,(
    ! [D_169,C_173,A_172,E_171,B_170] : k3_enumset1(A_172,B_170,C_173,D_169,E_171) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2268])).

tff(c_2387,plain,(
    ! [A_174,B_175,C_176,D_177] : k2_enumset1(A_174,B_175,C_176,D_177) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2384])).

tff(c_2390,plain,(
    ! [A_178,B_179,C_180] : k1_enumset1(A_178,B_179,C_180) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2387])).

tff(c_2392,plain,(
    ! [A_22,B_23] : k2_tarski(A_22,B_23) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2390])).

tff(c_955,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_941,c_207])).

tff(c_2394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2392,c_955])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:53:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.54  
% 3.45/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.54  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.45/1.54  
% 3.45/1.54  %Foreground sorts:
% 3.45/1.54  
% 3.45/1.54  
% 3.45/1.54  %Background operators:
% 3.45/1.54  
% 3.45/1.54  
% 3.45/1.54  %Foreground operators:
% 3.45/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.45/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.45/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.45/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.45/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.45/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.45/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.45/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.45/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.45/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.45/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.45/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.45/1.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.45/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.45/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.45/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.45/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.45/1.54  
% 3.52/1.56  tff(f_47, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.52/1.56  tff(f_49, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.52/1.56  tff(f_51, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.52/1.56  tff(f_53, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.52/1.56  tff(f_43, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 3.52/1.56  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.52/1.56  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.52/1.56  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.52/1.56  tff(f_66, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 3.52/1.56  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.52/1.56  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.52/1.56  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.52/1.56  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.52/1.56  tff(f_62, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.52/1.56  tff(c_22, plain, (![A_22, B_23]: (k1_enumset1(A_22, A_22, B_23)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.52/1.56  tff(c_24, plain, (![A_24, B_25, C_26]: (k2_enumset1(A_24, A_24, B_25, C_26)=k1_enumset1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.52/1.56  tff(c_26, plain, (![A_27, B_28, C_29, D_30]: (k3_enumset1(A_27, A_27, B_28, C_29, D_30)=k2_enumset1(A_27, B_28, C_29, D_30))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.52/1.56  tff(c_28, plain, (![A_31, C_33, B_32, E_35, D_34]: (k4_enumset1(A_31, A_31, B_32, C_33, D_34, E_35)=k3_enumset1(A_31, B_32, C_33, D_34, E_35))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.52/1.56  tff(c_18, plain, (![B_16, A_15, D_18, E_19, F_20, C_17]: (k2_xboole_0(k1_tarski(A_15), k3_enumset1(B_16, C_17, D_18, E_19, F_20))=k4_enumset1(A_15, B_16, C_17, D_18, E_19, F_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.52/1.56  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.52/1.56  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.52/1.56  tff(c_185, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.52/1.56  tff(c_194, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k4_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_185])).
% 3.52/1.56  tff(c_198, plain, (![A_72]: (k4_xboole_0(A_72, k1_xboole_0)=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_194])).
% 3.52/1.56  tff(c_38, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.52/1.56  tff(c_6, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k2_xboole_0(A_4, B_5))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.52/1.56  tff(c_92, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_38, c_6])).
% 3.52/1.56  tff(c_207, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_198, c_92])).
% 3.52/1.56  tff(c_218, plain, (k2_xboole_0(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_207, c_38])).
% 3.52/1.56  tff(c_16, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.52/1.56  tff(c_204, plain, (![A_72]: (k5_xboole_0(k1_xboole_0, A_72)=k2_xboole_0(k1_xboole_0, A_72))), inference(superposition, [status(thm), theory('equality')], [c_198, c_16])).
% 3.52/1.56  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.52/1.56  tff(c_552, plain, (![A_89, B_90, C_91]: (k5_xboole_0(k5_xboole_0(A_89, B_90), C_91)=k5_xboole_0(A_89, k5_xboole_0(B_90, C_91)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.52/1.56  tff(c_827, plain, (![A_105, B_106]: (k5_xboole_0(A_105, k5_xboole_0(B_106, k5_xboole_0(A_105, B_106)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_552])).
% 3.52/1.56  tff(c_879, plain, (![A_8]: (k5_xboole_0(A_8, k5_xboole_0(k1_xboole_0, A_8))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_827])).
% 3.52/1.56  tff(c_895, plain, (![A_107]: (k5_xboole_0(A_107, k2_xboole_0(k1_xboole_0, A_107))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_204, c_879])).
% 3.52/1.56  tff(c_932, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_218, c_895])).
% 3.52/1.56  tff(c_941, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_932])).
% 3.52/1.56  tff(c_36, plain, (![A_51, B_52]: (k2_xboole_0(k1_tarski(A_51), B_52)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.52/1.56  tff(c_1248, plain, (![A_129, B_130]: (k2_xboole_0(k1_tarski(A_129), B_130)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_941, c_36])).
% 3.52/1.56  tff(c_2268, plain, (![F_163, C_160, D_161, A_165, E_164, B_162]: (k4_enumset1(A_165, B_162, C_160, D_161, E_164, F_163)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_1248])).
% 3.52/1.56  tff(c_2384, plain, (![D_169, C_173, A_172, E_171, B_170]: (k3_enumset1(A_172, B_170, C_173, D_169, E_171)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_2268])).
% 3.52/1.56  tff(c_2387, plain, (![A_174, B_175, C_176, D_177]: (k2_enumset1(A_174, B_175, C_176, D_177)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_2384])).
% 3.52/1.56  tff(c_2390, plain, (![A_178, B_179, C_180]: (k1_enumset1(A_178, B_179, C_180)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_2387])).
% 3.52/1.56  tff(c_2392, plain, (![A_22, B_23]: (k2_tarski(A_22, B_23)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_2390])).
% 3.52/1.56  tff(c_955, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_941, c_207])).
% 3.52/1.56  tff(c_2394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2392, c_955])).
% 3.52/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.56  
% 3.52/1.56  Inference rules
% 3.52/1.56  ----------------------
% 3.52/1.56  #Ref     : 0
% 3.52/1.56  #Sup     : 566
% 3.52/1.56  #Fact    : 0
% 3.52/1.56  #Define  : 0
% 3.52/1.56  #Split   : 0
% 3.52/1.56  #Chain   : 0
% 3.52/1.56  #Close   : 0
% 3.52/1.56  
% 3.52/1.56  Ordering : KBO
% 3.52/1.56  
% 3.52/1.56  Simplification rules
% 3.52/1.56  ----------------------
% 3.52/1.56  #Subsume      : 7
% 3.52/1.56  #Demod        : 456
% 3.52/1.56  #Tautology    : 439
% 3.52/1.56  #SimpNegUnit  : 1
% 3.52/1.56  #BackRed      : 32
% 3.52/1.56  
% 3.52/1.56  #Partial instantiations: 0
% 3.52/1.56  #Strategies tried      : 1
% 3.52/1.56  
% 3.52/1.56  Timing (in seconds)
% 3.52/1.56  ----------------------
% 3.52/1.56  Preprocessing        : 0.31
% 3.52/1.56  Parsing              : 0.17
% 3.52/1.56  CNF conversion       : 0.02
% 3.52/1.56  Main loop            : 0.48
% 3.52/1.56  Inferencing          : 0.18
% 3.52/1.56  Reduction            : 0.19
% 3.52/1.56  Demodulation         : 0.16
% 3.52/1.56  BG Simplification    : 0.02
% 3.52/1.56  Subsumption          : 0.06
% 3.52/1.56  Abstraction          : 0.03
% 3.52/1.56  MUC search           : 0.00
% 3.52/1.56  Cooper               : 0.00
% 3.52/1.56  Total                : 0.82
% 3.52/1.56  Index Insertion      : 0.00
% 3.52/1.56  Index Deletion       : 0.00
% 3.52/1.56  Index Matching       : 0.00
% 3.52/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
