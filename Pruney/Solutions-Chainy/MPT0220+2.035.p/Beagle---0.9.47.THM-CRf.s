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
% DateTime   : Thu Dec  3 09:48:08 EST 2020

% Result     : Theorem 5.70s
% Output     : CNFRefutation 5.70s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 233 expanded)
%              Number of leaves         :   30 (  91 expanded)
%              Depth                    :   15
%              Number of atoms          :   52 ( 244 expanded)
%              Number of equality atoms :   41 ( 169 expanded)
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

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

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

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_12,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_57,plain,(
    ! [A_50,B_51] : r1_tarski(k4_xboole_0(A_50,B_51),A_50) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_60,plain,(
    ! [A_12] : r1_tarski(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_57])).

tff(c_143,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(A_62,B_63) = k1_xboole_0
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_160,plain,(
    ! [A_64] : k4_xboole_0(A_64,A_64) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_143])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_180,plain,(
    ! [A_65] : r1_tarski(k1_xboole_0,A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_14])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_184,plain,(
    ! [A_65] : k4_xboole_0(k1_xboole_0,A_65) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_180,c_8])).

tff(c_298,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k4_xboole_0(B_76,A_75)) = k2_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_313,plain,(
    ! [A_65] : k5_xboole_0(A_65,k1_xboole_0) = k2_xboole_0(A_65,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_298])).

tff(c_333,plain,(
    ! [A_80] : k5_xboole_0(A_80,k1_xboole_0) = A_80 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_313])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_339,plain,(
    ! [A_80] : k5_xboole_0(k1_xboole_0,A_80) = A_80 ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_4])).

tff(c_20,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_416,plain,(
    ! [A_82,B_83,C_84] : k5_xboole_0(k5_xboole_0(A_82,B_83),C_84) = k5_xboole_0(A_82,k5_xboole_0(B_83,C_84)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_734,plain,(
    ! [C_108,A_109,B_110] : k5_xboole_0(C_108,k5_xboole_0(A_109,B_110)) = k5_xboole_0(A_109,k5_xboole_0(B_110,C_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_4])).

tff(c_920,plain,(
    ! [A_111,C_112] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_111,C_112)) = k5_xboole_0(C_112,A_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_734])).

tff(c_982,plain,(
    ! [B_17,A_16] : k5_xboole_0(k4_xboole_0(B_17,A_16),A_16) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_920])).

tff(c_1008,plain,(
    ! [B_17,A_16] : k5_xboole_0(k4_xboole_0(B_17,A_16),A_16) = k2_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_982])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_283,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_292,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_283])).

tff(c_967,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_920])).

tff(c_1005,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k4_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_967])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3506,plain,(
    ! [A_149,B_150,C_151] : k5_xboole_0(A_149,k5_xboole_0(k3_xboole_0(A_149,B_150),C_151)) = k5_xboole_0(k4_xboole_0(A_149,B_150),C_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_416])).

tff(c_3658,plain,(
    ! [B_2,A_1] : k5_xboole_0(k4_xboole_0(B_2,A_1),A_1) = k5_xboole_0(B_2,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1005,c_3506])).

tff(c_3746,plain,(
    ! [B_152,A_153] : k2_xboole_0(B_152,A_153) = k2_xboole_0(A_153,B_152) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_20,c_3658])).

tff(c_36,plain,(
    ! [A_46,B_47] : r1_tarski(k1_tarski(A_46),k2_tarski(A_46,B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_157,plain,(
    ! [A_46,B_47] : k4_xboole_0(k1_tarski(A_46),k2_tarski(A_46,B_47)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_143])).

tff(c_1103,plain,(
    ! [B_122,A_123] : k5_xboole_0(k4_xboole_0(B_122,A_123),A_123) = k2_xboole_0(A_123,B_122) ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_982])).

tff(c_1154,plain,(
    ! [A_46,B_47] : k2_xboole_0(k2_tarski(A_46,B_47),k1_tarski(A_46)) = k5_xboole_0(k1_xboole_0,k2_tarski(A_46,B_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_1103])).

tff(c_1184,plain,(
    ! [A_46,B_47] : k2_xboole_0(k2_tarski(A_46,B_47),k1_tarski(A_46)) = k2_tarski(A_46,B_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_1154])).

tff(c_3761,plain,(
    ! [A_46,B_47] : k2_xboole_0(k1_tarski(A_46),k2_tarski(A_46,B_47)) = k2_tarski(A_46,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_3746,c_1184])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3829,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3761,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:25:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.70/2.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.70/2.15  
% 5.70/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.70/2.16  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 5.70/2.16  
% 5.70/2.16  %Foreground sorts:
% 5.70/2.16  
% 5.70/2.16  
% 5.70/2.16  %Background operators:
% 5.70/2.16  
% 5.70/2.16  
% 5.70/2.16  %Foreground operators:
% 5.70/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.70/2.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.70/2.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.70/2.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.70/2.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.70/2.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.70/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.70/2.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.70/2.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.70/2.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.70/2.16  tff('#skF_2', type, '#skF_2': $i).
% 5.70/2.16  tff('#skF_1', type, '#skF_1': $i).
% 5.70/2.16  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.70/2.16  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.70/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.70/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.70/2.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.70/2.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.70/2.16  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.70/2.16  
% 5.70/2.17  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.70/2.17  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.70/2.17  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.70/2.17  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.70/2.17  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.70/2.17  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.70/2.17  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.70/2.17  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.70/2.17  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.70/2.17  tff(f_61, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 5.70/2.17  tff(f_64, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 5.70/2.17  tff(c_12, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.70/2.17  tff(c_16, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.70/2.17  tff(c_57, plain, (![A_50, B_51]: (r1_tarski(k4_xboole_0(A_50, B_51), A_50))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.70/2.17  tff(c_60, plain, (![A_12]: (r1_tarski(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_57])).
% 5.70/2.17  tff(c_143, plain, (![A_62, B_63]: (k4_xboole_0(A_62, B_63)=k1_xboole_0 | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.70/2.17  tff(c_160, plain, (![A_64]: (k4_xboole_0(A_64, A_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_143])).
% 5.70/2.17  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.70/2.17  tff(c_180, plain, (![A_65]: (r1_tarski(k1_xboole_0, A_65))), inference(superposition, [status(thm), theory('equality')], [c_160, c_14])).
% 5.70/2.17  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.70/2.17  tff(c_184, plain, (![A_65]: (k4_xboole_0(k1_xboole_0, A_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_180, c_8])).
% 5.70/2.17  tff(c_298, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k4_xboole_0(B_76, A_75))=k2_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.70/2.17  tff(c_313, plain, (![A_65]: (k5_xboole_0(A_65, k1_xboole_0)=k2_xboole_0(A_65, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_184, c_298])).
% 5.70/2.17  tff(c_333, plain, (![A_80]: (k5_xboole_0(A_80, k1_xboole_0)=A_80)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_313])).
% 5.70/2.17  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.70/2.17  tff(c_339, plain, (![A_80]: (k5_xboole_0(k1_xboole_0, A_80)=A_80)), inference(superposition, [status(thm), theory('equality')], [c_333, c_4])).
% 5.70/2.17  tff(c_20, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.70/2.17  tff(c_416, plain, (![A_82, B_83, C_84]: (k5_xboole_0(k5_xboole_0(A_82, B_83), C_84)=k5_xboole_0(A_82, k5_xboole_0(B_83, C_84)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.70/2.17  tff(c_734, plain, (![C_108, A_109, B_110]: (k5_xboole_0(C_108, k5_xboole_0(A_109, B_110))=k5_xboole_0(A_109, k5_xboole_0(B_110, C_108)))), inference(superposition, [status(thm), theory('equality')], [c_416, c_4])).
% 5.70/2.17  tff(c_920, plain, (![A_111, C_112]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_111, C_112))=k5_xboole_0(C_112, A_111))), inference(superposition, [status(thm), theory('equality')], [c_339, c_734])).
% 5.70/2.17  tff(c_982, plain, (![B_17, A_16]: (k5_xboole_0(k4_xboole_0(B_17, A_16), A_16)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_920])).
% 5.70/2.17  tff(c_1008, plain, (![B_17, A_16]: (k5_xboole_0(k4_xboole_0(B_17, A_16), A_16)=k2_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_339, c_982])).
% 5.70/2.17  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.70/2.17  tff(c_283, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.70/2.17  tff(c_292, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_283])).
% 5.70/2.17  tff(c_967, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_292, c_920])).
% 5.70/2.17  tff(c_1005, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k4_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_339, c_967])).
% 5.70/2.17  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.70/2.17  tff(c_3506, plain, (![A_149, B_150, C_151]: (k5_xboole_0(A_149, k5_xboole_0(k3_xboole_0(A_149, B_150), C_151))=k5_xboole_0(k4_xboole_0(A_149, B_150), C_151))), inference(superposition, [status(thm), theory('equality')], [c_10, c_416])).
% 5.70/2.17  tff(c_3658, plain, (![B_2, A_1]: (k5_xboole_0(k4_xboole_0(B_2, A_1), A_1)=k5_xboole_0(B_2, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_1005, c_3506])).
% 5.70/2.17  tff(c_3746, plain, (![B_152, A_153]: (k2_xboole_0(B_152, A_153)=k2_xboole_0(A_153, B_152))), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_20, c_3658])).
% 5.70/2.17  tff(c_36, plain, (![A_46, B_47]: (r1_tarski(k1_tarski(A_46), k2_tarski(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.70/2.17  tff(c_157, plain, (![A_46, B_47]: (k4_xboole_0(k1_tarski(A_46), k2_tarski(A_46, B_47))=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_143])).
% 5.70/2.17  tff(c_1103, plain, (![B_122, A_123]: (k5_xboole_0(k4_xboole_0(B_122, A_123), A_123)=k2_xboole_0(A_123, B_122))), inference(demodulation, [status(thm), theory('equality')], [c_339, c_982])).
% 5.70/2.17  tff(c_1154, plain, (![A_46, B_47]: (k2_xboole_0(k2_tarski(A_46, B_47), k1_tarski(A_46))=k5_xboole_0(k1_xboole_0, k2_tarski(A_46, B_47)))), inference(superposition, [status(thm), theory('equality')], [c_157, c_1103])).
% 5.70/2.17  tff(c_1184, plain, (![A_46, B_47]: (k2_xboole_0(k2_tarski(A_46, B_47), k1_tarski(A_46))=k2_tarski(A_46, B_47))), inference(demodulation, [status(thm), theory('equality')], [c_339, c_1154])).
% 5.70/2.17  tff(c_3761, plain, (![A_46, B_47]: (k2_xboole_0(k1_tarski(A_46), k2_tarski(A_46, B_47))=k2_tarski(A_46, B_47))), inference(superposition, [status(thm), theory('equality')], [c_3746, c_1184])).
% 5.70/2.17  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.70/2.17  tff(c_3829, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3761, c_38])).
% 5.70/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.70/2.17  
% 5.70/2.17  Inference rules
% 5.70/2.17  ----------------------
% 5.70/2.17  #Ref     : 0
% 5.70/2.17  #Sup     : 960
% 5.70/2.17  #Fact    : 0
% 5.70/2.17  #Define  : 0
% 5.70/2.17  #Split   : 0
% 5.70/2.17  #Chain   : 0
% 5.70/2.17  #Close   : 0
% 5.70/2.17  
% 5.70/2.17  Ordering : KBO
% 5.70/2.17  
% 5.70/2.17  Simplification rules
% 5.70/2.17  ----------------------
% 5.70/2.17  #Subsume      : 125
% 5.70/2.17  #Demod        : 564
% 5.70/2.17  #Tautology    : 329
% 5.70/2.17  #SimpNegUnit  : 0
% 5.70/2.17  #BackRed      : 1
% 5.70/2.17  
% 5.70/2.17  #Partial instantiations: 0
% 5.70/2.17  #Strategies tried      : 1
% 5.70/2.17  
% 5.70/2.17  Timing (in seconds)
% 5.70/2.17  ----------------------
% 5.70/2.18  Preprocessing        : 0.33
% 5.70/2.18  Parsing              : 0.18
% 5.70/2.18  CNF conversion       : 0.02
% 5.70/2.18  Main loop            : 1.08
% 5.70/2.18  Inferencing          : 0.27
% 5.70/2.18  Reduction            : 0.62
% 5.70/2.18  Demodulation         : 0.56
% 5.70/2.18  BG Simplification    : 0.05
% 5.70/2.18  Subsumption          : 0.10
% 5.70/2.18  Abstraction          : 0.06
% 5.70/2.18  MUC search           : 0.00
% 5.70/2.18  Cooper               : 0.00
% 5.70/2.18  Total                : 1.45
% 5.70/2.18  Index Insertion      : 0.00
% 5.70/2.18  Index Deletion       : 0.00
% 5.70/2.18  Index Matching       : 0.00
% 5.70/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
