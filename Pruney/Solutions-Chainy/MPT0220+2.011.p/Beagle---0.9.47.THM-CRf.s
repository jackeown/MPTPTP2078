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
% DateTime   : Thu Dec  3 09:48:05 EST 2020

% Result     : Theorem 8.99s
% Output     : CNFRefutation 8.99s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 446 expanded)
%              Number of leaves         :   30 ( 165 expanded)
%              Depth                    :   20
%              Number of atoms          :   63 ( 565 expanded)
%              Number of equality atoms :   53 ( 390 expanded)
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

tff(f_43,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_18,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_134,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k1_xboole_0
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_142,plain,(
    ! [B_6] : k4_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_134])).

tff(c_159,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_167,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_159])).

tff(c_213,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k4_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_222,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_213])).

tff(c_231,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_222])).

tff(c_422,plain,(
    ! [A_88,B_89,C_90] : k5_xboole_0(k5_xboole_0(A_88,B_89),C_90) = k5_xboole_0(A_88,k5_xboole_0(B_89,C_90)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_509,plain,(
    ! [A_91,B_92] : k5_xboole_0(A_91,k5_xboole_0(B_92,k5_xboole_0(A_91,B_92))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_231])).

tff(c_570,plain,(
    ! [B_93] : k5_xboole_0(B_93,k5_xboole_0(B_93,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_509])).

tff(c_661,plain,(
    ! [A_95] : k5_xboole_0(A_95,k5_xboole_0(k1_xboole_0,A_95)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_570])).

tff(c_4268,plain,(
    ! [B_150] : k5_xboole_0(k3_xboole_0(k1_xboole_0,B_150),k4_xboole_0(k1_xboole_0,B_150)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_661])).

tff(c_768,plain,(
    ! [B_100,C_101] : k5_xboole_0(B_100,k5_xboole_0(B_100,C_101)) = k5_xboole_0(k1_xboole_0,C_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_422])).

tff(c_861,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = k5_xboole_0(k1_xboole_0,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_768])).

tff(c_4288,plain,(
    ! [B_150] : k5_xboole_0(k4_xboole_0(k1_xboole_0,B_150),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,B_150)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4268,c_861])).

tff(c_4316,plain,(
    ! [B_150] : k5_xboole_0(k4_xboole_0(k1_xboole_0,B_150),k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_4288])).

tff(c_4883,plain,(
    ! [A_159,B_160,C_161] : k5_xboole_0(A_159,k5_xboole_0(k4_xboole_0(B_160,A_159),C_161)) = k5_xboole_0(k2_xboole_0(A_159,B_160),C_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_422])).

tff(c_4971,plain,(
    ! [B_150] : k5_xboole_0(k2_xboole_0(B_150,k1_xboole_0),k1_xboole_0) = k5_xboole_0(B_150,k4_xboole_0(k1_xboole_0,B_150)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4316,c_4883])).

tff(c_5074,plain,(
    ! [B_150] : k5_xboole_0(B_150,k1_xboole_0) = B_150 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_24,c_18,c_4971])).

tff(c_549,plain,(
    ! [B_6] : k5_xboole_0(B_6,k5_xboole_0(B_6,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_509])).

tff(c_892,plain,(
    ! [A_107,B_108] : k5_xboole_0(A_107,k5_xboole_0(B_108,A_107)) = k5_xboole_0(k1_xboole_0,B_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_768])).

tff(c_949,plain,(
    ! [B_6] : k5_xboole_0(k5_xboole_0(B_6,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_892])).

tff(c_5093,plain,(
    ! [B_6] : k5_xboole_0(k1_xboole_0,B_6) = B_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5074,c_5074,c_949])).

tff(c_40,plain,(
    ! [A_47,B_48] : r1_tarski(k1_tarski(A_47),k2_tarski(A_47,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_141,plain,(
    ! [A_47,B_48] : k4_xboole_0(k1_tarski(A_47),k2_tarski(A_47,B_48)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_134])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_225,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_213])).

tff(c_2063,plain,(
    ! [C_135,A_136,B_137] : k5_xboole_0(C_135,k5_xboole_0(A_136,B_137)) = k5_xboole_0(A_136,k5_xboole_0(B_137,C_135)) ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_4])).

tff(c_2447,plain,(
    ! [B_6,A_136] : k5_xboole_0(B_6,k5_xboole_0(A_136,B_6)) = k5_xboole_0(A_136,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_2063])).

tff(c_5660,plain,(
    ! [B_170,A_171] : k5_xboole_0(B_170,k5_xboole_0(A_171,B_170)) = A_171 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5074,c_2447])).

tff(c_479,plain,(
    ! [A_9,B_10,C_90] : k5_xboole_0(A_9,k5_xboole_0(k3_xboole_0(A_9,B_10),C_90)) = k5_xboole_0(k4_xboole_0(A_9,B_10),C_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_422])).

tff(c_9942,plain,(
    ! [B_221,B_222] : k5_xboole_0(k4_xboole_0(B_221,B_222),B_221) = k3_xboole_0(B_221,B_222) ),
    inference(superposition,[status(thm),theory(equality)],[c_5660,c_479])).

tff(c_486,plain,(
    ! [A_17,B_18,C_90] : k5_xboole_0(A_17,k5_xboole_0(k4_xboole_0(B_18,A_17),C_90)) = k5_xboole_0(k2_xboole_0(A_17,B_18),C_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_422])).

tff(c_10004,plain,(
    ! [B_222,B_221] : k5_xboole_0(k2_xboole_0(B_222,B_221),B_221) = k5_xboole_0(B_222,k3_xboole_0(B_221,B_222)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9942,c_486])).

tff(c_11781,plain,(
    ! [B_237,B_238] : k5_xboole_0(k2_xboole_0(B_237,B_238),B_238) = k4_xboole_0(B_237,B_238) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_10004])).

tff(c_5088,plain,(
    ! [B_6,A_136] : k5_xboole_0(B_6,k5_xboole_0(A_136,B_6)) = A_136 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5074,c_2447])).

tff(c_12167,plain,(
    ! [B_243,B_244] : k5_xboole_0(B_243,k4_xboole_0(B_244,B_243)) = k2_xboole_0(B_244,B_243) ),
    inference(superposition,[status(thm),theory(equality)],[c_11781,c_5088])).

tff(c_12301,plain,(
    ! [A_47,B_48] : k2_xboole_0(k1_tarski(A_47),k2_tarski(A_47,B_48)) = k5_xboole_0(k2_tarski(A_47,B_48),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_12167])).

tff(c_12325,plain,(
    ! [A_47,B_48] : k2_xboole_0(k1_tarski(A_47),k2_tarski(A_47,B_48)) = k2_tarski(A_47,B_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5093,c_4,c_12301])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12325,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:36:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.99/3.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.99/3.71  
% 8.99/3.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.99/3.71  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 8.99/3.71  
% 8.99/3.71  %Foreground sorts:
% 8.99/3.71  
% 8.99/3.71  
% 8.99/3.71  %Background operators:
% 8.99/3.71  
% 8.99/3.71  
% 8.99/3.71  %Foreground operators:
% 8.99/3.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.99/3.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.99/3.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.99/3.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.99/3.71  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.99/3.71  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.99/3.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.99/3.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.99/3.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.99/3.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.99/3.71  tff('#skF_2', type, '#skF_2': $i).
% 8.99/3.71  tff('#skF_1', type, '#skF_1': $i).
% 8.99/3.71  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.99/3.71  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.99/3.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.99/3.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.99/3.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.99/3.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.99/3.71  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.99/3.71  
% 8.99/3.73  tff(f_43, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 8.99/3.73  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.99/3.73  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.99/3.73  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.99/3.73  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.99/3.73  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.99/3.73  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.99/3.73  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.99/3.73  tff(f_67, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 8.99/3.73  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.99/3.73  tff(f_70, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 8.99/3.73  tff(c_18, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.99/3.73  tff(c_24, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.99/3.73  tff(c_16, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.99/3.73  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.99/3.73  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.99/3.73  tff(c_134, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k1_xboole_0 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.99/3.73  tff(c_142, plain, (![B_6]: (k4_xboole_0(B_6, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_134])).
% 8.99/3.73  tff(c_159, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.99/3.73  tff(c_167, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_159])).
% 8.99/3.73  tff(c_213, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k4_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.99/3.73  tff(c_222, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_167, c_213])).
% 8.99/3.73  tff(c_231, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_142, c_222])).
% 8.99/3.73  tff(c_422, plain, (![A_88, B_89, C_90]: (k5_xboole_0(k5_xboole_0(A_88, B_89), C_90)=k5_xboole_0(A_88, k5_xboole_0(B_89, C_90)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.99/3.73  tff(c_509, plain, (![A_91, B_92]: (k5_xboole_0(A_91, k5_xboole_0(B_92, k5_xboole_0(A_91, B_92)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_422, c_231])).
% 8.99/3.73  tff(c_570, plain, (![B_93]: (k5_xboole_0(B_93, k5_xboole_0(B_93, k1_xboole_0))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_231, c_509])).
% 8.99/3.73  tff(c_661, plain, (![A_95]: (k5_xboole_0(A_95, k5_xboole_0(k1_xboole_0, A_95))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_570])).
% 8.99/3.73  tff(c_4268, plain, (![B_150]: (k5_xboole_0(k3_xboole_0(k1_xboole_0, B_150), k4_xboole_0(k1_xboole_0, B_150))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_661])).
% 8.99/3.73  tff(c_768, plain, (![B_100, C_101]: (k5_xboole_0(B_100, k5_xboole_0(B_100, C_101))=k5_xboole_0(k1_xboole_0, C_101))), inference(superposition, [status(thm), theory('equality')], [c_231, c_422])).
% 8.99/3.73  tff(c_861, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=k5_xboole_0(k1_xboole_0, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_768])).
% 8.99/3.73  tff(c_4288, plain, (![B_150]: (k5_xboole_0(k4_xboole_0(k1_xboole_0, B_150), k1_xboole_0)=k5_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, B_150)))), inference(superposition, [status(thm), theory('equality')], [c_4268, c_861])).
% 8.99/3.73  tff(c_4316, plain, (![B_150]: (k5_xboole_0(k4_xboole_0(k1_xboole_0, B_150), k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_150))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_4288])).
% 8.99/3.73  tff(c_4883, plain, (![A_159, B_160, C_161]: (k5_xboole_0(A_159, k5_xboole_0(k4_xboole_0(B_160, A_159), C_161))=k5_xboole_0(k2_xboole_0(A_159, B_160), C_161))), inference(superposition, [status(thm), theory('equality')], [c_24, c_422])).
% 8.99/3.73  tff(c_4971, plain, (![B_150]: (k5_xboole_0(k2_xboole_0(B_150, k1_xboole_0), k1_xboole_0)=k5_xboole_0(B_150, k4_xboole_0(k1_xboole_0, B_150)))), inference(superposition, [status(thm), theory('equality')], [c_4316, c_4883])).
% 8.99/3.73  tff(c_5074, plain, (![B_150]: (k5_xboole_0(B_150, k1_xboole_0)=B_150)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_24, c_18, c_4971])).
% 8.99/3.73  tff(c_549, plain, (![B_6]: (k5_xboole_0(B_6, k5_xboole_0(B_6, k1_xboole_0))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_231, c_509])).
% 8.99/3.73  tff(c_892, plain, (![A_107, B_108]: (k5_xboole_0(A_107, k5_xboole_0(B_108, A_107))=k5_xboole_0(k1_xboole_0, B_108))), inference(superposition, [status(thm), theory('equality')], [c_4, c_768])).
% 8.99/3.73  tff(c_949, plain, (![B_6]: (k5_xboole_0(k5_xboole_0(B_6, k1_xboole_0), k1_xboole_0)=k5_xboole_0(k1_xboole_0, B_6))), inference(superposition, [status(thm), theory('equality')], [c_549, c_892])).
% 8.99/3.73  tff(c_5093, plain, (![B_6]: (k5_xboole_0(k1_xboole_0, B_6)=B_6)), inference(demodulation, [status(thm), theory('equality')], [c_5074, c_5074, c_949])).
% 8.99/3.73  tff(c_40, plain, (![A_47, B_48]: (r1_tarski(k1_tarski(A_47), k2_tarski(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.99/3.73  tff(c_141, plain, (![A_47, B_48]: (k4_xboole_0(k1_tarski(A_47), k2_tarski(A_47, B_48))=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_134])).
% 8.99/3.73  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.99/3.73  tff(c_225, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_213])).
% 8.99/3.73  tff(c_2063, plain, (![C_135, A_136, B_137]: (k5_xboole_0(C_135, k5_xboole_0(A_136, B_137))=k5_xboole_0(A_136, k5_xboole_0(B_137, C_135)))), inference(superposition, [status(thm), theory('equality')], [c_422, c_4])).
% 8.99/3.73  tff(c_2447, plain, (![B_6, A_136]: (k5_xboole_0(B_6, k5_xboole_0(A_136, B_6))=k5_xboole_0(A_136, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_231, c_2063])).
% 8.99/3.73  tff(c_5660, plain, (![B_170, A_171]: (k5_xboole_0(B_170, k5_xboole_0(A_171, B_170))=A_171)), inference(demodulation, [status(thm), theory('equality')], [c_5074, c_2447])).
% 8.99/3.73  tff(c_479, plain, (![A_9, B_10, C_90]: (k5_xboole_0(A_9, k5_xboole_0(k3_xboole_0(A_9, B_10), C_90))=k5_xboole_0(k4_xboole_0(A_9, B_10), C_90))), inference(superposition, [status(thm), theory('equality')], [c_16, c_422])).
% 8.99/3.73  tff(c_9942, plain, (![B_221, B_222]: (k5_xboole_0(k4_xboole_0(B_221, B_222), B_221)=k3_xboole_0(B_221, B_222))), inference(superposition, [status(thm), theory('equality')], [c_5660, c_479])).
% 8.99/3.73  tff(c_486, plain, (![A_17, B_18, C_90]: (k5_xboole_0(A_17, k5_xboole_0(k4_xboole_0(B_18, A_17), C_90))=k5_xboole_0(k2_xboole_0(A_17, B_18), C_90))), inference(superposition, [status(thm), theory('equality')], [c_24, c_422])).
% 8.99/3.73  tff(c_10004, plain, (![B_222, B_221]: (k5_xboole_0(k2_xboole_0(B_222, B_221), B_221)=k5_xboole_0(B_222, k3_xboole_0(B_221, B_222)))), inference(superposition, [status(thm), theory('equality')], [c_9942, c_486])).
% 8.99/3.73  tff(c_11781, plain, (![B_237, B_238]: (k5_xboole_0(k2_xboole_0(B_237, B_238), B_238)=k4_xboole_0(B_237, B_238))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_10004])).
% 8.99/3.73  tff(c_5088, plain, (![B_6, A_136]: (k5_xboole_0(B_6, k5_xboole_0(A_136, B_6))=A_136)), inference(demodulation, [status(thm), theory('equality')], [c_5074, c_2447])).
% 8.99/3.73  tff(c_12167, plain, (![B_243, B_244]: (k5_xboole_0(B_243, k4_xboole_0(B_244, B_243))=k2_xboole_0(B_244, B_243))), inference(superposition, [status(thm), theory('equality')], [c_11781, c_5088])).
% 8.99/3.73  tff(c_12301, plain, (![A_47, B_48]: (k2_xboole_0(k1_tarski(A_47), k2_tarski(A_47, B_48))=k5_xboole_0(k2_tarski(A_47, B_48), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_141, c_12167])).
% 8.99/3.73  tff(c_12325, plain, (![A_47, B_48]: (k2_xboole_0(k1_tarski(A_47), k2_tarski(A_47, B_48))=k2_tarski(A_47, B_48))), inference(demodulation, [status(thm), theory('equality')], [c_5093, c_4, c_12301])).
% 8.99/3.73  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.99/3.73  tff(c_14813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12325, c_42])).
% 8.99/3.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.99/3.73  
% 8.99/3.73  Inference rules
% 8.99/3.73  ----------------------
% 8.99/3.73  #Ref     : 0
% 8.99/3.73  #Sup     : 3636
% 8.99/3.73  #Fact    : 0
% 8.99/3.73  #Define  : 0
% 8.99/3.73  #Split   : 0
% 8.99/3.73  #Chain   : 0
% 8.99/3.73  #Close   : 0
% 8.99/3.73  
% 8.99/3.73  Ordering : KBO
% 8.99/3.73  
% 8.99/3.73  Simplification rules
% 8.99/3.73  ----------------------
% 8.99/3.73  #Subsume      : 220
% 8.99/3.73  #Demod        : 4244
% 8.99/3.73  #Tautology    : 1966
% 8.99/3.73  #SimpNegUnit  : 0
% 8.99/3.73  #BackRed      : 30
% 8.99/3.73  
% 8.99/3.73  #Partial instantiations: 0
% 8.99/3.73  #Strategies tried      : 1
% 8.99/3.73  
% 8.99/3.73  Timing (in seconds)
% 8.99/3.73  ----------------------
% 8.99/3.73  Preprocessing        : 0.32
% 8.99/3.73  Parsing              : 0.17
% 8.99/3.73  CNF conversion       : 0.02
% 8.99/3.73  Main loop            : 2.64
% 8.99/3.73  Inferencing          : 0.54
% 8.99/3.73  Reduction            : 1.63
% 8.99/3.73  Demodulation         : 1.50
% 8.99/3.73  BG Simplification    : 0.08
% 8.99/3.73  Subsumption          : 0.27
% 8.99/3.73  Abstraction          : 0.11
% 8.99/3.73  MUC search           : 0.00
% 8.99/3.73  Cooper               : 0.00
% 8.99/3.73  Total                : 2.99
% 8.99/3.73  Index Insertion      : 0.00
% 8.99/3.73  Index Deletion       : 0.00
% 8.99/3.73  Index Matching       : 0.00
% 8.99/3.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
