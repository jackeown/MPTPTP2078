%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:07 EST 2020

% Result     : Theorem 7.16s
% Output     : CNFRefutation 7.16s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 136 expanded)
%              Number of leaves         :   31 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :   61 ( 123 expanded)
%              Number of equality atoms :   53 ( 113 expanded)
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

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_75,plain,(
    ! [B_56,A_57] : k5_xboole_0(B_56,A_57) = k5_xboole_0(A_57,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_91,plain,(
    ! [A_57] : k5_xboole_0(k1_xboole_0,A_57) = A_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_20])).

tff(c_24,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_596,plain,(
    ! [A_87,B_88,C_89] : k5_xboole_0(k5_xboole_0(A_87,B_88),C_89) = k5_xboole_0(A_87,k5_xboole_0(B_88,C_89)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1888,plain,(
    ! [C_146,A_147,B_148] : k5_xboole_0(C_146,k5_xboole_0(A_147,B_148)) = k5_xboole_0(A_147,k5_xboole_0(B_148,C_146)) ),
    inference(superposition,[status(thm),theory(equality)],[c_596,c_4])).

tff(c_2268,plain,(
    ! [A_149,C_150] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_149,C_150)) = k5_xboole_0(C_150,A_149) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_1888])).

tff(c_2385,plain,(
    ! [B_19,A_18] : k5_xboole_0(k4_xboole_0(B_19,A_18),A_18) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_18,B_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2268])).

tff(c_2435,plain,(
    ! [B_19,A_18] : k5_xboole_0(k4_xboole_0(B_19,A_18),A_18) = k2_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_2385])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_237,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = k4_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_256,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_237])).

tff(c_2379,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_2268])).

tff(c_2433,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k4_xboole_0(B_2,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_2379])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4485,plain,(
    ! [A_180,B_181,C_182] : k5_xboole_0(A_180,k5_xboole_0(k3_xboole_0(A_180,B_181),C_182)) = k5_xboole_0(k4_xboole_0(A_180,B_181),C_182) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_596])).

tff(c_4574,plain,(
    ! [A_1,B_2] : k5_xboole_0(k4_xboole_0(A_1,B_2),B_2) = k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2433,c_4485])).

tff(c_4697,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2435,c_24,c_4574])).

tff(c_18,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_380,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k4_xboole_0(B_76,A_75)) = k2_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_403,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = k2_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_380])).

tff(c_411,plain,(
    ! [A_77] : k2_xboole_0(A_77,k1_xboole_0) = A_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_403])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_423,plain,(
    ! [A_78] : k4_xboole_0(A_78,A_78) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_16])).

tff(c_428,plain,(
    ! [A_78] : k5_xboole_0(A_78,k1_xboole_0) = k2_xboole_0(A_78,A_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_24])).

tff(c_446,plain,(
    ! [A_78] : k2_xboole_0(A_78,A_78) = A_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_428])).

tff(c_417,plain,(
    ! [A_77] : k4_xboole_0(A_77,A_77) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_16])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_210,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_218,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_210])).

tff(c_250,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_237])).

tff(c_519,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_250])).

tff(c_40,plain,(
    ! [A_48,B_49] : r1_tarski(k1_tarski(A_48),k2_tarski(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1150,plain,(
    ! [A_115,B_116] : k3_xboole_0(k1_tarski(A_115),k2_tarski(A_115,B_116)) = k1_tarski(A_115) ),
    inference(resolution,[status(thm)],[c_40,c_210])).

tff(c_1159,plain,(
    ! [A_115,B_116] : k5_xboole_0(k1_tarski(A_115),k1_tarski(A_115)) = k4_xboole_0(k1_tarski(A_115),k2_tarski(A_115,B_116)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1150,c_12])).

tff(c_1170,plain,(
    ! [A_117,B_118] : k4_xboole_0(k1_tarski(A_117),k2_tarski(A_117,B_118)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_1159])).

tff(c_1175,plain,(
    ! [A_117,B_118] : k2_xboole_0(k2_tarski(A_117,B_118),k1_tarski(A_117)) = k5_xboole_0(k2_tarski(A_117,B_118),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1170,c_24])).

tff(c_11569,plain,(
    ! [A_249,B_250] : k2_xboole_0(k2_tarski(A_249,B_250),k1_tarski(A_249)) = k2_tarski(A_249,B_250) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1175])).

tff(c_396,plain,(
    ! [A_11,B_12] : k5_xboole_0(k2_xboole_0(A_11,B_12),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_11,B_12),A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_380])).

tff(c_408,plain,(
    ! [A_11,B_12] : k2_xboole_0(k2_xboole_0(A_11,B_12),A_11) = k2_xboole_0(A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_396])).

tff(c_11665,plain,(
    ! [A_249,B_250] : k2_xboole_0(k2_tarski(A_249,B_250),k2_tarski(A_249,B_250)) = k2_xboole_0(k2_tarski(A_249,B_250),k1_tarski(A_249)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11569,c_408])).

tff(c_11703,plain,(
    ! [A_249,B_250] : k2_xboole_0(k1_tarski(A_249),k2_tarski(A_249,B_250)) = k2_tarski(A_249,B_250) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4697,c_446,c_11665])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_11710,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11703,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:01:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.16/2.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.16/2.93  
% 7.16/2.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.16/2.93  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 7.16/2.93  
% 7.16/2.93  %Foreground sorts:
% 7.16/2.93  
% 7.16/2.93  
% 7.16/2.93  %Background operators:
% 7.16/2.93  
% 7.16/2.93  
% 7.16/2.93  %Foreground operators:
% 7.16/2.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.16/2.93  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.16/2.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.16/2.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.16/2.93  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.16/2.93  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.16/2.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.16/2.93  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.16/2.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.16/2.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.16/2.93  tff('#skF_2', type, '#skF_2': $i).
% 7.16/2.93  tff('#skF_1', type, '#skF_1': $i).
% 7.16/2.93  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.16/2.93  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.16/2.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.16/2.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.16/2.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.16/2.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.16/2.93  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.16/2.93  
% 7.16/2.95  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.16/2.95  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 7.16/2.95  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.16/2.95  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.16/2.95  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.16/2.95  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.16/2.95  tff(f_45, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 7.16/2.95  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 7.16/2.95  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.16/2.95  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.16/2.95  tff(f_67, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 7.16/2.95  tff(f_70, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 7.16/2.95  tff(c_75, plain, (![B_56, A_57]: (k5_xboole_0(B_56, A_57)=k5_xboole_0(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.16/2.95  tff(c_20, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.16/2.95  tff(c_91, plain, (![A_57]: (k5_xboole_0(k1_xboole_0, A_57)=A_57)), inference(superposition, [status(thm), theory('equality')], [c_75, c_20])).
% 7.16/2.95  tff(c_24, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.16/2.95  tff(c_596, plain, (![A_87, B_88, C_89]: (k5_xboole_0(k5_xboole_0(A_87, B_88), C_89)=k5_xboole_0(A_87, k5_xboole_0(B_88, C_89)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.16/2.95  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.16/2.95  tff(c_1888, plain, (![C_146, A_147, B_148]: (k5_xboole_0(C_146, k5_xboole_0(A_147, B_148))=k5_xboole_0(A_147, k5_xboole_0(B_148, C_146)))), inference(superposition, [status(thm), theory('equality')], [c_596, c_4])).
% 7.16/2.95  tff(c_2268, plain, (![A_149, C_150]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_149, C_150))=k5_xboole_0(C_150, A_149))), inference(superposition, [status(thm), theory('equality')], [c_91, c_1888])).
% 7.16/2.95  tff(c_2385, plain, (![B_19, A_18]: (k5_xboole_0(k4_xboole_0(B_19, A_18), A_18)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_18, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2268])).
% 7.16/2.95  tff(c_2435, plain, (![B_19, A_18]: (k5_xboole_0(k4_xboole_0(B_19, A_18), A_18)=k2_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_2385])).
% 7.16/2.95  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.16/2.95  tff(c_237, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k3_xboole_0(A_68, B_69))=k4_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.16/2.95  tff(c_256, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_237])).
% 7.16/2.95  tff(c_2379, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k5_xboole_0(k1_xboole_0, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_256, c_2268])).
% 7.16/2.95  tff(c_2433, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k4_xboole_0(B_2, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_2379])).
% 7.16/2.95  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.16/2.95  tff(c_4485, plain, (![A_180, B_181, C_182]: (k5_xboole_0(A_180, k5_xboole_0(k3_xboole_0(A_180, B_181), C_182))=k5_xboole_0(k4_xboole_0(A_180, B_181), C_182))), inference(superposition, [status(thm), theory('equality')], [c_12, c_596])).
% 7.16/2.95  tff(c_4574, plain, (![A_1, B_2]: (k5_xboole_0(k4_xboole_0(A_1, B_2), B_2)=k5_xboole_0(A_1, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2433, c_4485])).
% 7.16/2.95  tff(c_4697, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_2435, c_24, c_4574])).
% 7.16/2.95  tff(c_18, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.16/2.95  tff(c_380, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k4_xboole_0(B_76, A_75))=k2_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.16/2.95  tff(c_403, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=k2_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_380])).
% 7.16/2.95  tff(c_411, plain, (![A_77]: (k2_xboole_0(A_77, k1_xboole_0)=A_77)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_403])).
% 7.16/2.95  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.16/2.95  tff(c_423, plain, (![A_78]: (k4_xboole_0(A_78, A_78)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_411, c_16])).
% 7.16/2.95  tff(c_428, plain, (![A_78]: (k5_xboole_0(A_78, k1_xboole_0)=k2_xboole_0(A_78, A_78))), inference(superposition, [status(thm), theory('equality')], [c_423, c_24])).
% 7.16/2.95  tff(c_446, plain, (![A_78]: (k2_xboole_0(A_78, A_78)=A_78)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_428])).
% 7.16/2.95  tff(c_417, plain, (![A_77]: (k4_xboole_0(A_77, A_77)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_411, c_16])).
% 7.16/2.95  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.16/2.95  tff(c_210, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.16/2.95  tff(c_218, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_210])).
% 7.16/2.95  tff(c_250, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_218, c_237])).
% 7.16/2.95  tff(c_519, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_417, c_250])).
% 7.16/2.95  tff(c_40, plain, (![A_48, B_49]: (r1_tarski(k1_tarski(A_48), k2_tarski(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.16/2.95  tff(c_1150, plain, (![A_115, B_116]: (k3_xboole_0(k1_tarski(A_115), k2_tarski(A_115, B_116))=k1_tarski(A_115))), inference(resolution, [status(thm)], [c_40, c_210])).
% 7.16/2.95  tff(c_1159, plain, (![A_115, B_116]: (k5_xboole_0(k1_tarski(A_115), k1_tarski(A_115))=k4_xboole_0(k1_tarski(A_115), k2_tarski(A_115, B_116)))), inference(superposition, [status(thm), theory('equality')], [c_1150, c_12])).
% 7.16/2.95  tff(c_1170, plain, (![A_117, B_118]: (k4_xboole_0(k1_tarski(A_117), k2_tarski(A_117, B_118))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_519, c_1159])).
% 7.16/2.95  tff(c_1175, plain, (![A_117, B_118]: (k2_xboole_0(k2_tarski(A_117, B_118), k1_tarski(A_117))=k5_xboole_0(k2_tarski(A_117, B_118), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1170, c_24])).
% 7.16/2.95  tff(c_11569, plain, (![A_249, B_250]: (k2_xboole_0(k2_tarski(A_249, B_250), k1_tarski(A_249))=k2_tarski(A_249, B_250))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1175])).
% 7.16/2.95  tff(c_396, plain, (![A_11, B_12]: (k5_xboole_0(k2_xboole_0(A_11, B_12), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_11, B_12), A_11))), inference(superposition, [status(thm), theory('equality')], [c_16, c_380])).
% 7.16/2.95  tff(c_408, plain, (![A_11, B_12]: (k2_xboole_0(k2_xboole_0(A_11, B_12), A_11)=k2_xboole_0(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_396])).
% 7.16/2.95  tff(c_11665, plain, (![A_249, B_250]: (k2_xboole_0(k2_tarski(A_249, B_250), k2_tarski(A_249, B_250))=k2_xboole_0(k2_tarski(A_249, B_250), k1_tarski(A_249)))), inference(superposition, [status(thm), theory('equality')], [c_11569, c_408])).
% 7.16/2.95  tff(c_11703, plain, (![A_249, B_250]: (k2_xboole_0(k1_tarski(A_249), k2_tarski(A_249, B_250))=k2_tarski(A_249, B_250))), inference(demodulation, [status(thm), theory('equality')], [c_4697, c_446, c_11665])).
% 7.16/2.95  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.16/2.95  tff(c_11710, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11703, c_42])).
% 7.16/2.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.16/2.95  
% 7.16/2.95  Inference rules
% 7.16/2.95  ----------------------
% 7.16/2.95  #Ref     : 0
% 7.16/2.95  #Sup     : 2920
% 7.16/2.95  #Fact    : 0
% 7.16/2.95  #Define  : 0
% 7.16/2.95  #Split   : 0
% 7.16/2.95  #Chain   : 0
% 7.16/2.95  #Close   : 0
% 7.16/2.95  
% 7.16/2.95  Ordering : KBO
% 7.16/2.95  
% 7.16/2.95  Simplification rules
% 7.16/2.95  ----------------------
% 7.16/2.95  #Subsume      : 173
% 7.16/2.95  #Demod        : 3208
% 7.16/2.95  #Tautology    : 1622
% 7.16/2.95  #SimpNegUnit  : 0
% 7.16/2.95  #BackRed      : 1
% 7.16/2.95  
% 7.16/2.95  #Partial instantiations: 0
% 7.16/2.95  #Strategies tried      : 1
% 7.16/2.95  
% 7.16/2.95  Timing (in seconds)
% 7.16/2.95  ----------------------
% 7.16/2.95  Preprocessing        : 0.32
% 7.16/2.95  Parsing              : 0.17
% 7.16/2.95  CNF conversion       : 0.02
% 7.16/2.95  Main loop            : 1.88
% 7.16/2.95  Inferencing          : 0.43
% 7.16/2.95  Reduction            : 1.10
% 7.16/2.95  Demodulation         : 1.00
% 7.16/2.95  BG Simplification    : 0.06
% 7.16/2.95  Subsumption          : 0.21
% 7.16/2.95  Abstraction          : 0.09
% 7.16/2.95  MUC search           : 0.00
% 7.16/2.95  Cooper               : 0.00
% 7.16/2.95  Total                : 2.23
% 7.16/2.95  Index Insertion      : 0.00
% 7.16/2.95  Index Deletion       : 0.00
% 7.16/2.95  Index Matching       : 0.00
% 7.16/2.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
