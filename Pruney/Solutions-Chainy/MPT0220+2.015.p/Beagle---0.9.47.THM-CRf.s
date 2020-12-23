%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:05 EST 2020

% Result     : Theorem 11.35s
% Output     : CNFRefutation 11.40s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 194 expanded)
%              Number of leaves         :   30 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :   51 ( 177 expanded)
%              Number of equality atoms :   46 ( 172 expanded)
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

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_14,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_323,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k4_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_241,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k4_xboole_0(B_73,A_72)) = k2_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_250,plain,(
    ! [A_14] : k5_xboole_0(k1_xboole_0,A_14) = k2_xboole_0(k1_xboole_0,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_241])).

tff(c_330,plain,(
    ! [B_77] : k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,B_77)) = k4_xboole_0(k1_xboole_0,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_250])).

tff(c_351,plain,(
    ! [B_78] : k4_xboole_0(k1_xboole_0,B_78) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_330])).

tff(c_26,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_356,plain,(
    ! [B_78] : k5_xboole_0(B_78,k1_xboole_0) = k2_xboole_0(B_78,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_26])).

tff(c_368,plain,(
    ! [B_78] : k5_xboole_0(B_78,k1_xboole_0) = B_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_356])).

tff(c_253,plain,(
    ! [A_74] : k5_xboole_0(k1_xboole_0,A_74) = k2_xboole_0(k1_xboole_0,A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_241])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_263,plain,(
    ! [A_74] : k5_xboole_0(A_74,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_4])).

tff(c_373,plain,(
    ! [A_74] : k2_xboole_0(k1_xboole_0,A_74) = A_74 ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_263])).

tff(c_407,plain,(
    ! [A_14] : k5_xboole_0(k1_xboole_0,A_14) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_250])).

tff(c_671,plain,(
    ! [A_91,B_92,C_93] : k5_xboole_0(k5_xboole_0(A_91,B_92),C_93) = k5_xboole_0(A_91,k5_xboole_0(B_92,C_93)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2350,plain,(
    ! [C_157,A_158,B_159] : k5_xboole_0(C_157,k5_xboole_0(A_158,B_159)) = k5_xboole_0(A_158,k5_xboole_0(B_159,C_157)) ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_4])).

tff(c_2750,plain,(
    ! [A_160,C_161] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_160,C_161)) = k5_xboole_0(C_161,A_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_2350])).

tff(c_2879,plain,(
    ! [B_21,A_20] : k5_xboole_0(k4_xboole_0(B_21,A_20),A_20) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2750])).

tff(c_2919,plain,(
    ! [B_21,A_20] : k5_xboole_0(k4_xboole_0(B_21,A_20),A_20) = k2_xboole_0(A_20,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_2879])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_343,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_323])).

tff(c_2838,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_2750])).

tff(c_2908,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k4_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_2838])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6728,plain,(
    ! [A_217,B_218,C_219] : k5_xboole_0(A_217,k5_xboole_0(k3_xboole_0(A_217,B_218),C_219)) = k5_xboole_0(k4_xboole_0(A_217,B_218),C_219) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_671])).

tff(c_6839,plain,(
    ! [B_2,A_1] : k5_xboole_0(k4_xboole_0(B_2,A_1),A_1) = k5_xboole_0(B_2,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2908,c_6728])).

tff(c_6968,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2919,c_26,c_6839])).

tff(c_42,plain,(
    ! [A_50,B_51] : r1_tarski(k1_tarski(A_50),k2_tarski(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_188,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(A_66,B_67) = A_66
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1307,plain,(
    ! [A_128,B_129] : k3_xboole_0(k1_tarski(A_128),k2_tarski(A_128,B_129)) = k1_tarski(A_128) ),
    inference(resolution,[status(thm)],[c_42,c_188])).

tff(c_121,plain,(
    ! [B_62,A_63] : k3_xboole_0(B_62,A_63) = k3_xboole_0(A_63,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_136,plain,(
    ! [A_63,B_62] : k2_xboole_0(A_63,k3_xboole_0(B_62,A_63)) = A_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_16])).

tff(c_9344,plain,(
    ! [A_246,B_247] : k2_xboole_0(k2_tarski(A_246,B_247),k1_tarski(A_246)) = k2_tarski(A_246,B_247) ),
    inference(superposition,[status(thm),theory(equality)],[c_1307,c_136])).

tff(c_9395,plain,(
    ! [A_246,B_247] : k2_xboole_0(k1_tarski(A_246),k2_tarski(A_246,B_247)) = k2_tarski(A_246,B_247) ),
    inference(superposition,[status(thm),theory(equality)],[c_6968,c_9344])).

tff(c_44,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12840,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9395,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.35/5.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.40/5.10  
% 11.40/5.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.40/5.10  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 11.40/5.10  
% 11.40/5.10  %Foreground sorts:
% 11.40/5.10  
% 11.40/5.10  
% 11.40/5.10  %Background operators:
% 11.40/5.10  
% 11.40/5.10  
% 11.40/5.10  %Foreground operators:
% 11.40/5.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.40/5.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.40/5.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.40/5.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.40/5.10  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.40/5.10  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.40/5.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.40/5.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.40/5.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.40/5.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.40/5.10  tff('#skF_2', type, '#skF_2': $i).
% 11.40/5.10  tff('#skF_1', type, '#skF_1': $i).
% 11.40/5.10  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.40/5.10  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.40/5.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.40/5.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.40/5.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.40/5.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.40/5.10  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.40/5.10  
% 11.40/5.12  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 11.40/5.12  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 11.40/5.12  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.40/5.12  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 11.40/5.12  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 11.40/5.12  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 11.40/5.12  tff(f_51, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.40/5.12  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.40/5.12  tff(f_69, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 11.40/5.12  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.40/5.12  tff(f_72, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 11.40/5.12  tff(c_14, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.40/5.12  tff(c_16, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k3_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.40/5.12  tff(c_323, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k4_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.40/5.12  tff(c_20, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.40/5.12  tff(c_241, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k4_xboole_0(B_73, A_72))=k2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.40/5.12  tff(c_250, plain, (![A_14]: (k5_xboole_0(k1_xboole_0, A_14)=k2_xboole_0(k1_xboole_0, A_14))), inference(superposition, [status(thm), theory('equality')], [c_20, c_241])).
% 11.40/5.12  tff(c_330, plain, (![B_77]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, B_77))=k4_xboole_0(k1_xboole_0, B_77))), inference(superposition, [status(thm), theory('equality')], [c_323, c_250])).
% 11.40/5.12  tff(c_351, plain, (![B_78]: (k4_xboole_0(k1_xboole_0, B_78)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_330])).
% 11.40/5.12  tff(c_26, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.40/5.12  tff(c_356, plain, (![B_78]: (k5_xboole_0(B_78, k1_xboole_0)=k2_xboole_0(B_78, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_351, c_26])).
% 11.40/5.12  tff(c_368, plain, (![B_78]: (k5_xboole_0(B_78, k1_xboole_0)=B_78)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_356])).
% 11.40/5.12  tff(c_253, plain, (![A_74]: (k5_xboole_0(k1_xboole_0, A_74)=k2_xboole_0(k1_xboole_0, A_74))), inference(superposition, [status(thm), theory('equality')], [c_20, c_241])).
% 11.40/5.12  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.40/5.12  tff(c_263, plain, (![A_74]: (k5_xboole_0(A_74, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_74))), inference(superposition, [status(thm), theory('equality')], [c_253, c_4])).
% 11.40/5.12  tff(c_373, plain, (![A_74]: (k2_xboole_0(k1_xboole_0, A_74)=A_74)), inference(demodulation, [status(thm), theory('equality')], [c_368, c_263])).
% 11.40/5.12  tff(c_407, plain, (![A_14]: (k5_xboole_0(k1_xboole_0, A_14)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_373, c_250])).
% 11.40/5.12  tff(c_671, plain, (![A_91, B_92, C_93]: (k5_xboole_0(k5_xboole_0(A_91, B_92), C_93)=k5_xboole_0(A_91, k5_xboole_0(B_92, C_93)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.40/5.12  tff(c_2350, plain, (![C_157, A_158, B_159]: (k5_xboole_0(C_157, k5_xboole_0(A_158, B_159))=k5_xboole_0(A_158, k5_xboole_0(B_159, C_157)))), inference(superposition, [status(thm), theory('equality')], [c_671, c_4])).
% 11.40/5.12  tff(c_2750, plain, (![A_160, C_161]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_160, C_161))=k5_xboole_0(C_161, A_160))), inference(superposition, [status(thm), theory('equality')], [c_407, c_2350])).
% 11.40/5.12  tff(c_2879, plain, (![B_21, A_20]: (k5_xboole_0(k4_xboole_0(B_21, A_20), A_20)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2750])).
% 11.40/5.12  tff(c_2919, plain, (![B_21, A_20]: (k5_xboole_0(k4_xboole_0(B_21, A_20), A_20)=k2_xboole_0(A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_407, c_2879])).
% 11.40/5.12  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.40/5.12  tff(c_343, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_323])).
% 11.40/5.12  tff(c_2838, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_343, c_2750])).
% 11.40/5.12  tff(c_2908, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k4_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_407, c_2838])).
% 11.40/5.12  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.40/5.12  tff(c_6728, plain, (![A_217, B_218, C_219]: (k5_xboole_0(A_217, k5_xboole_0(k3_xboole_0(A_217, B_218), C_219))=k5_xboole_0(k4_xboole_0(A_217, B_218), C_219))), inference(superposition, [status(thm), theory('equality')], [c_12, c_671])).
% 11.40/5.12  tff(c_6839, plain, (![B_2, A_1]: (k5_xboole_0(k4_xboole_0(B_2, A_1), A_1)=k5_xboole_0(B_2, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2908, c_6728])).
% 11.40/5.12  tff(c_6968, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_2919, c_26, c_6839])).
% 11.40/5.12  tff(c_42, plain, (![A_50, B_51]: (r1_tarski(k1_tarski(A_50), k2_tarski(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.40/5.12  tff(c_188, plain, (![A_66, B_67]: (k3_xboole_0(A_66, B_67)=A_66 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.40/5.12  tff(c_1307, plain, (![A_128, B_129]: (k3_xboole_0(k1_tarski(A_128), k2_tarski(A_128, B_129))=k1_tarski(A_128))), inference(resolution, [status(thm)], [c_42, c_188])).
% 11.40/5.12  tff(c_121, plain, (![B_62, A_63]: (k3_xboole_0(B_62, A_63)=k3_xboole_0(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.40/5.12  tff(c_136, plain, (![A_63, B_62]: (k2_xboole_0(A_63, k3_xboole_0(B_62, A_63))=A_63)), inference(superposition, [status(thm), theory('equality')], [c_121, c_16])).
% 11.40/5.12  tff(c_9344, plain, (![A_246, B_247]: (k2_xboole_0(k2_tarski(A_246, B_247), k1_tarski(A_246))=k2_tarski(A_246, B_247))), inference(superposition, [status(thm), theory('equality')], [c_1307, c_136])).
% 11.40/5.12  tff(c_9395, plain, (![A_246, B_247]: (k2_xboole_0(k1_tarski(A_246), k2_tarski(A_246, B_247))=k2_tarski(A_246, B_247))), inference(superposition, [status(thm), theory('equality')], [c_6968, c_9344])).
% 11.40/5.12  tff(c_44, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.40/5.12  tff(c_12840, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9395, c_44])).
% 11.40/5.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.40/5.12  
% 11.40/5.12  Inference rules
% 11.40/5.12  ----------------------
% 11.40/5.12  #Ref     : 0
% 11.40/5.12  #Sup     : 3186
% 11.40/5.12  #Fact    : 0
% 11.40/5.12  #Define  : 0
% 11.40/5.12  #Split   : 0
% 11.40/5.12  #Chain   : 0
% 11.40/5.12  #Close   : 0
% 11.40/5.12  
% 11.40/5.12  Ordering : KBO
% 11.40/5.13  
% 11.40/5.13  Simplification rules
% 11.40/5.13  ----------------------
% 11.40/5.13  #Subsume      : 185
% 11.40/5.13  #Demod        : 3721
% 11.40/5.13  #Tautology    : 1870
% 11.40/5.13  #SimpNegUnit  : 0
% 11.40/5.13  #BackRed      : 3
% 11.40/5.13  
% 11.40/5.13  #Partial instantiations: 0
% 11.40/5.13  #Strategies tried      : 1
% 11.40/5.13  
% 11.40/5.13  Timing (in seconds)
% 11.40/5.13  ----------------------
% 11.40/5.13  Preprocessing        : 0.51
% 11.40/5.13  Parsing              : 0.26
% 11.40/5.13  CNF conversion       : 0.03
% 11.40/5.13  Main loop            : 3.68
% 11.40/5.13  Inferencing          : 0.77
% 11.40/5.13  Reduction            : 2.23
% 11.40/5.13  Demodulation         : 2.03
% 11.40/5.13  BG Simplification    : 0.12
% 11.51/5.13  Subsumption          : 0.41
% 11.51/5.13  Abstraction          : 0.17
% 11.51/5.13  MUC search           : 0.00
% 11.51/5.13  Cooper               : 0.00
% 11.51/5.13  Total                : 4.24
% 11.51/5.13  Index Insertion      : 0.00
% 11.51/5.13  Index Deletion       : 0.00
% 11.51/5.13  Index Matching       : 0.00
% 11.51/5.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
