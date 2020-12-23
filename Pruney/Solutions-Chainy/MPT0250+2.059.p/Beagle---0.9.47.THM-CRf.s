%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:39 EST 2020

% Result     : Theorem 4.98s
% Output     : CNFRefutation 5.41s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 686 expanded)
%              Number of leaves         :   33 ( 246 expanded)
%              Depth                    :   24
%              Number of atoms          :   77 ( 672 expanded)
%              Number of equality atoms :   66 ( 659 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(c_48,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_19] : k4_xboole_0(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_288,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k4_xboole_0(B_86,A_85)) = k2_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_300,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = k2_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_288])).

tff(c_303,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_300])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_315,plain,(
    ! [A_88,B_89] : k5_xboole_0(A_88,k3_xboole_0(A_88,B_89)) = k4_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_333,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = k4_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_315])).

tff(c_338,plain,(
    ! [A_90] : k4_xboole_0(A_90,k1_xboole_0) = A_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_333])).

tff(c_18,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_347,plain,(
    ! [A_90] : k4_xboole_0(A_90,A_90) = k3_xboole_0(A_90,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_18])).

tff(c_360,plain,(
    ! [A_90] : k4_xboole_0(A_90,A_90) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_347])).

tff(c_337,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_333])).

tff(c_364,plain,(
    ! [A_91] : k4_xboole_0(A_91,A_91) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_347])).

tff(c_376,plain,(
    ! [A_91] : k4_xboole_0(A_91,k1_xboole_0) = k3_xboole_0(A_91,A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_18])).

tff(c_416,plain,(
    ! [A_93] : k3_xboole_0(A_93,A_93) = A_93 ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_376])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_422,plain,(
    ! [A_93] : k5_xboole_0(A_93,A_93) = k4_xboole_0(A_93,A_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_4])).

tff(c_443,plain,(
    ! [A_93] : k5_xboole_0(A_93,A_93) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_422])).

tff(c_392,plain,(
    ! [A_91] : k3_xboole_0(A_91,A_91) = A_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_376])).

tff(c_696,plain,(
    ! [A_114,B_115,C_116] : k3_xboole_0(k3_xboole_0(A_114,B_115),C_116) = k3_xboole_0(A_114,k3_xboole_0(B_115,C_116)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_775,plain,(
    ! [A_117,C_118] : k3_xboole_0(A_117,k3_xboole_0(A_117,C_118)) = k3_xboole_0(A_117,C_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_696])).

tff(c_327,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_315])).

tff(c_798,plain,(
    ! [A_117,C_118] : k5_xboole_0(k3_xboole_0(A_117,C_118),k3_xboole_0(A_117,C_118)) = k4_xboole_0(k3_xboole_0(A_117,C_118),A_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_775,c_327])).

tff(c_854,plain,(
    ! [A_119,C_120] : k4_xboole_0(k3_xboole_0(A_119,C_120),A_119) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_798])).

tff(c_890,plain,(
    ! [B_2,A_1] : k4_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_854])).

tff(c_1071,plain,(
    ! [A_131,B_132,C_133] : k5_xboole_0(k3_xboole_0(A_131,B_132),k3_xboole_0(C_133,B_132)) = k3_xboole_0(k5_xboole_0(A_131,C_133),B_132) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1082,plain,(
    ! [A_131,B_132] : k3_xboole_0(k5_xboole_0(A_131,k3_xboole_0(A_131,B_132)),B_132) = k4_xboole_0(k3_xboole_0(A_131,B_132),B_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_1071,c_4])).

tff(c_1149,plain,(
    ! [B_134,A_135] : k3_xboole_0(B_134,k4_xboole_0(A_135,B_134)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_890,c_2,c_4,c_1082])).

tff(c_1192,plain,(
    ! [B_134,A_135] : k4_xboole_0(B_134,k4_xboole_0(A_135,B_134)) = k5_xboole_0(B_134,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1149,c_4])).

tff(c_1237,plain,(
    ! [B_134,A_135] : k4_xboole_0(B_134,k4_xboole_0(A_135,B_134)) = B_134 ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_1192])).

tff(c_22,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1104,plain,(
    ! [A_91,C_133] : k5_xboole_0(A_91,k3_xboole_0(C_133,A_91)) = k3_xboole_0(k5_xboole_0(A_91,C_133),A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_1071])).

tff(c_1442,plain,(
    ! [A_144,C_145] : k3_xboole_0(A_144,k5_xboole_0(A_144,C_145)) = k4_xboole_0(A_144,C_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_2,c_1104])).

tff(c_1518,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k3_xboole_0(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1442])).

tff(c_1530,plain,(
    ! [A_20,B_21] : k3_xboole_0(A_20,k2_xboole_0(A_20,B_21)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1237,c_1518])).

tff(c_50,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1685,plain,(
    ! [A_155,B_156] : k3_xboole_0(A_155,k2_xboole_0(A_155,B_156)) = A_155 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1237,c_1518])).

tff(c_1900,plain,(
    ! [A_167,B_168] :
      ( k3_xboole_0(A_167,B_168) = A_167
      | ~ r1_tarski(A_167,B_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1685])).

tff(c_1904,plain,(
    k3_xboole_0(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') = k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1900])).

tff(c_3014,plain,(
    ! [C_204,A_205,B_206] : k3_xboole_0(C_204,k3_xboole_0(A_205,B_206)) = k3_xboole_0(A_205,k3_xboole_0(B_206,C_204)) ),
    inference(superposition,[status(thm),theory(equality)],[c_696,c_2])).

tff(c_843,plain,(
    ! [A_117,C_118] : k4_xboole_0(k3_xboole_0(A_117,C_118),A_117) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_798])).

tff(c_4595,plain,(
    ! [A_222,B_223,C_224] : k4_xboole_0(k3_xboole_0(A_222,k3_xboole_0(B_223,C_224)),C_224) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3014,c_843])).

tff(c_5765,plain,(
    ! [A_235] : k4_xboole_0(k3_xboole_0(A_235,k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1904,c_4595])).

tff(c_5827,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1530,c_5765])).

tff(c_1142,plain,(
    ! [A_91,C_133] : k3_xboole_0(A_91,k5_xboole_0(A_91,C_133)) = k4_xboole_0(A_91,C_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_2,c_1104])).

tff(c_738,plain,(
    ! [A_91,C_116] : k3_xboole_0(A_91,k3_xboole_0(A_91,C_116)) = k3_xboole_0(A_91,C_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_696])).

tff(c_1466,plain,(
    ! [A_144,C_145] : k3_xboole_0(A_144,k5_xboole_0(A_144,C_145)) = k3_xboole_0(A_144,k4_xboole_0(A_144,C_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1442,c_738])).

tff(c_2233,plain,(
    ! [A_194,C_195] : k3_xboole_0(A_194,k4_xboole_0(A_194,C_195)) = k4_xboole_0(A_194,C_195) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1142,c_1466])).

tff(c_2284,plain,(
    ! [A_194,C_195] : k5_xboole_0(A_194,k4_xboole_0(A_194,C_195)) = k4_xboole_0(A_194,k4_xboole_0(A_194,C_195)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2233,c_4])).

tff(c_2351,plain,(
    ! [A_194,C_195] : k5_xboole_0(A_194,k4_xboole_0(A_194,C_195)) = k3_xboole_0(A_194,C_195) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2284])).

tff(c_5876,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_xboole_0) = k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5827,c_2351])).

tff(c_5909,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_2,c_5876])).

tff(c_44,plain,(
    ! [B_65,A_64] :
      ( r2_hidden(B_65,A_64)
      | k3_xboole_0(A_64,k1_tarski(B_65)) != k1_tarski(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6019,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5909,c_44])).

tff(c_6051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_6019])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 13:15:55 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.98/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.33/2.08  
% 5.33/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.33/2.08  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 5.33/2.08  
% 5.33/2.08  %Foreground sorts:
% 5.33/2.08  
% 5.33/2.08  
% 5.33/2.08  %Background operators:
% 5.33/2.08  
% 5.33/2.08  
% 5.33/2.08  %Foreground operators:
% 5.33/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.33/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.33/2.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.33/2.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.33/2.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.33/2.08  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.33/2.08  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.33/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.33/2.08  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.33/2.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.33/2.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.33/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.33/2.08  tff('#skF_1', type, '#skF_1': $i).
% 5.33/2.08  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.33/2.08  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.33/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.33/2.08  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.33/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.33/2.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.33/2.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.33/2.08  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.33/2.08  
% 5.41/2.10  tff(f_80, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 5.41/2.10  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.41/2.10  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 5.41/2.10  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.41/2.10  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.41/2.10  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.41/2.10  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.41/2.10  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.41/2.10  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 5.41/2.10  tff(f_33, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 5.41/2.10  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 5.41/2.10  tff(f_73, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 5.41/2.10  tff(c_48, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.41/2.10  tff(c_12, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.41/2.10  tff(c_20, plain, (![A_19]: (k4_xboole_0(k1_xboole_0, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.41/2.10  tff(c_288, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k4_xboole_0(B_86, A_85))=k2_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.41/2.10  tff(c_300, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=k2_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_288])).
% 5.41/2.10  tff(c_303, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_300])).
% 5.41/2.10  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.41/2.10  tff(c_14, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.41/2.10  tff(c_315, plain, (![A_88, B_89]: (k5_xboole_0(A_88, k3_xboole_0(A_88, B_89))=k4_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.41/2.10  tff(c_333, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=k4_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_315])).
% 5.41/2.10  tff(c_338, plain, (![A_90]: (k4_xboole_0(A_90, k1_xboole_0)=A_90)), inference(demodulation, [status(thm), theory('equality')], [c_303, c_333])).
% 5.41/2.10  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.41/2.10  tff(c_347, plain, (![A_90]: (k4_xboole_0(A_90, A_90)=k3_xboole_0(A_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_338, c_18])).
% 5.41/2.10  tff(c_360, plain, (![A_90]: (k4_xboole_0(A_90, A_90)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_347])).
% 5.41/2.10  tff(c_337, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_303, c_333])).
% 5.41/2.10  tff(c_364, plain, (![A_91]: (k4_xboole_0(A_91, A_91)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_347])).
% 5.41/2.10  tff(c_376, plain, (![A_91]: (k4_xboole_0(A_91, k1_xboole_0)=k3_xboole_0(A_91, A_91))), inference(superposition, [status(thm), theory('equality')], [c_364, c_18])).
% 5.41/2.10  tff(c_416, plain, (![A_93]: (k3_xboole_0(A_93, A_93)=A_93)), inference(demodulation, [status(thm), theory('equality')], [c_337, c_376])).
% 5.41/2.10  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.41/2.10  tff(c_422, plain, (![A_93]: (k5_xboole_0(A_93, A_93)=k4_xboole_0(A_93, A_93))), inference(superposition, [status(thm), theory('equality')], [c_416, c_4])).
% 5.41/2.10  tff(c_443, plain, (![A_93]: (k5_xboole_0(A_93, A_93)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_360, c_422])).
% 5.41/2.10  tff(c_392, plain, (![A_91]: (k3_xboole_0(A_91, A_91)=A_91)), inference(demodulation, [status(thm), theory('equality')], [c_337, c_376])).
% 5.41/2.10  tff(c_696, plain, (![A_114, B_115, C_116]: (k3_xboole_0(k3_xboole_0(A_114, B_115), C_116)=k3_xboole_0(A_114, k3_xboole_0(B_115, C_116)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.41/2.10  tff(c_775, plain, (![A_117, C_118]: (k3_xboole_0(A_117, k3_xboole_0(A_117, C_118))=k3_xboole_0(A_117, C_118))), inference(superposition, [status(thm), theory('equality')], [c_392, c_696])).
% 5.41/2.10  tff(c_327, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_315])).
% 5.41/2.10  tff(c_798, plain, (![A_117, C_118]: (k5_xboole_0(k3_xboole_0(A_117, C_118), k3_xboole_0(A_117, C_118))=k4_xboole_0(k3_xboole_0(A_117, C_118), A_117))), inference(superposition, [status(thm), theory('equality')], [c_775, c_327])).
% 5.41/2.10  tff(c_854, plain, (![A_119, C_120]: (k4_xboole_0(k3_xboole_0(A_119, C_120), A_119)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_443, c_798])).
% 5.41/2.10  tff(c_890, plain, (![B_2, A_1]: (k4_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_854])).
% 5.41/2.10  tff(c_1071, plain, (![A_131, B_132, C_133]: (k5_xboole_0(k3_xboole_0(A_131, B_132), k3_xboole_0(C_133, B_132))=k3_xboole_0(k5_xboole_0(A_131, C_133), B_132))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.41/2.10  tff(c_1082, plain, (![A_131, B_132]: (k3_xboole_0(k5_xboole_0(A_131, k3_xboole_0(A_131, B_132)), B_132)=k4_xboole_0(k3_xboole_0(A_131, B_132), B_132))), inference(superposition, [status(thm), theory('equality')], [c_1071, c_4])).
% 5.41/2.10  tff(c_1149, plain, (![B_134, A_135]: (k3_xboole_0(B_134, k4_xboole_0(A_135, B_134))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_890, c_2, c_4, c_1082])).
% 5.41/2.10  tff(c_1192, plain, (![B_134, A_135]: (k4_xboole_0(B_134, k4_xboole_0(A_135, B_134))=k5_xboole_0(B_134, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1149, c_4])).
% 5.41/2.10  tff(c_1237, plain, (![B_134, A_135]: (k4_xboole_0(B_134, k4_xboole_0(A_135, B_134))=B_134)), inference(demodulation, [status(thm), theory('equality')], [c_303, c_1192])).
% 5.41/2.10  tff(c_22, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.41/2.10  tff(c_1104, plain, (![A_91, C_133]: (k5_xboole_0(A_91, k3_xboole_0(C_133, A_91))=k3_xboole_0(k5_xboole_0(A_91, C_133), A_91))), inference(superposition, [status(thm), theory('equality')], [c_392, c_1071])).
% 5.41/2.10  tff(c_1442, plain, (![A_144, C_145]: (k3_xboole_0(A_144, k5_xboole_0(A_144, C_145))=k4_xboole_0(A_144, C_145))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_2, c_1104])).
% 5.41/2.10  tff(c_1518, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k3_xboole_0(A_20, k2_xboole_0(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1442])).
% 5.41/2.10  tff(c_1530, plain, (![A_20, B_21]: (k3_xboole_0(A_20, k2_xboole_0(A_20, B_21))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_1237, c_1518])).
% 5.41/2.10  tff(c_50, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.41/2.10  tff(c_16, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k4_xboole_0(B_16, A_15))=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.41/2.10  tff(c_1685, plain, (![A_155, B_156]: (k3_xboole_0(A_155, k2_xboole_0(A_155, B_156))=A_155)), inference(demodulation, [status(thm), theory('equality')], [c_1237, c_1518])).
% 5.41/2.10  tff(c_1900, plain, (![A_167, B_168]: (k3_xboole_0(A_167, B_168)=A_167 | ~r1_tarski(A_167, B_168))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1685])).
% 5.41/2.10  tff(c_1904, plain, (k3_xboole_0(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')=k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_50, c_1900])).
% 5.41/2.10  tff(c_3014, plain, (![C_204, A_205, B_206]: (k3_xboole_0(C_204, k3_xboole_0(A_205, B_206))=k3_xboole_0(A_205, k3_xboole_0(B_206, C_204)))), inference(superposition, [status(thm), theory('equality')], [c_696, c_2])).
% 5.41/2.10  tff(c_843, plain, (![A_117, C_118]: (k4_xboole_0(k3_xboole_0(A_117, C_118), A_117)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_443, c_798])).
% 5.41/2.10  tff(c_4595, plain, (![A_222, B_223, C_224]: (k4_xboole_0(k3_xboole_0(A_222, k3_xboole_0(B_223, C_224)), C_224)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3014, c_843])).
% 5.41/2.10  tff(c_5765, plain, (![A_235]: (k4_xboole_0(k3_xboole_0(A_235, k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')), '#skF_2')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1904, c_4595])).
% 5.41/2.10  tff(c_5827, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1530, c_5765])).
% 5.41/2.10  tff(c_1142, plain, (![A_91, C_133]: (k3_xboole_0(A_91, k5_xboole_0(A_91, C_133))=k4_xboole_0(A_91, C_133))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_2, c_1104])).
% 5.41/2.10  tff(c_738, plain, (![A_91, C_116]: (k3_xboole_0(A_91, k3_xboole_0(A_91, C_116))=k3_xboole_0(A_91, C_116))), inference(superposition, [status(thm), theory('equality')], [c_392, c_696])).
% 5.41/2.10  tff(c_1466, plain, (![A_144, C_145]: (k3_xboole_0(A_144, k5_xboole_0(A_144, C_145))=k3_xboole_0(A_144, k4_xboole_0(A_144, C_145)))), inference(superposition, [status(thm), theory('equality')], [c_1442, c_738])).
% 5.41/2.10  tff(c_2233, plain, (![A_194, C_195]: (k3_xboole_0(A_194, k4_xboole_0(A_194, C_195))=k4_xboole_0(A_194, C_195))), inference(demodulation, [status(thm), theory('equality')], [c_1142, c_1466])).
% 5.41/2.10  tff(c_2284, plain, (![A_194, C_195]: (k5_xboole_0(A_194, k4_xboole_0(A_194, C_195))=k4_xboole_0(A_194, k4_xboole_0(A_194, C_195)))), inference(superposition, [status(thm), theory('equality')], [c_2233, c_4])).
% 5.41/2.10  tff(c_2351, plain, (![A_194, C_195]: (k5_xboole_0(A_194, k4_xboole_0(A_194, C_195))=k3_xboole_0(A_194, C_195))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2284])).
% 5.41/2.10  tff(c_5876, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_xboole_0)=k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5827, c_2351])).
% 5.41/2.10  tff(c_5909, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_303, c_2, c_5876])).
% 5.41/2.10  tff(c_44, plain, (![B_65, A_64]: (r2_hidden(B_65, A_64) | k3_xboole_0(A_64, k1_tarski(B_65))!=k1_tarski(B_65))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.41/2.10  tff(c_6019, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5909, c_44])).
% 5.41/2.10  tff(c_6051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_6019])).
% 5.41/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.41/2.10  
% 5.41/2.10  Inference rules
% 5.41/2.10  ----------------------
% 5.41/2.10  #Ref     : 0
% 5.41/2.10  #Sup     : 1514
% 5.41/2.10  #Fact    : 0
% 5.41/2.10  #Define  : 0
% 5.41/2.10  #Split   : 0
% 5.41/2.10  #Chain   : 0
% 5.41/2.10  #Close   : 0
% 5.41/2.10  
% 5.41/2.10  Ordering : KBO
% 5.41/2.10  
% 5.41/2.10  Simplification rules
% 5.41/2.10  ----------------------
% 5.41/2.10  #Subsume      : 27
% 5.41/2.10  #Demod        : 1466
% 5.41/2.10  #Tautology    : 970
% 5.41/2.10  #SimpNegUnit  : 1
% 5.41/2.10  #BackRed      : 0
% 5.41/2.10  
% 5.41/2.10  #Partial instantiations: 0
% 5.41/2.10  #Strategies tried      : 1
% 5.41/2.10  
% 5.41/2.10  Timing (in seconds)
% 5.41/2.10  ----------------------
% 5.41/2.10  Preprocessing        : 0.33
% 5.41/2.10  Parsing              : 0.18
% 5.41/2.10  CNF conversion       : 0.02
% 5.41/2.10  Main loop            : 0.97
% 5.41/2.10  Inferencing          : 0.29
% 5.41/2.10  Reduction            : 0.47
% 5.41/2.10  Demodulation         : 0.40
% 5.41/2.10  BG Simplification    : 0.04
% 5.41/2.10  Subsumption          : 0.13
% 5.41/2.11  Abstraction          : 0.05
% 5.41/2.11  MUC search           : 0.00
% 5.41/2.11  Cooper               : 0.00
% 5.41/2.11  Total                : 1.34
% 5.41/2.11  Index Insertion      : 0.00
% 5.41/2.11  Index Deletion       : 0.00
% 5.41/2.11  Index Matching       : 0.00
% 5.41/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
