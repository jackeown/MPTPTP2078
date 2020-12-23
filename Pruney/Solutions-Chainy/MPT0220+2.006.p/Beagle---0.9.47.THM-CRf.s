%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:04 EST 2020

% Result     : Theorem 10.68s
% Output     : CNFRefutation 10.84s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 106 expanded)
%              Number of leaves         :   30 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   57 (  99 expanded)
%              Number of equality atoms :   43 (  81 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_63,plain,(
    ! [B_42,A_43] : k5_xboole_0(B_42,A_43) = k5_xboole_0(A_43,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_79,plain,(
    ! [A_43] : k5_xboole_0(k1_xboole_0,A_43) = A_43 ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_22])).

tff(c_20,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_188,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1592,plain,(
    ! [A_109,B_110] : k3_xboole_0(k4_xboole_0(A_109,B_110),A_109) = k4_xboole_0(A_109,B_110) ),
    inference(resolution,[status(thm)],[c_20,c_188])).

tff(c_24,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_220,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = k1_xboole_0
      | ~ r1_xboole_0(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_228,plain,(
    ! [A_16,B_17] : k3_xboole_0(k4_xboole_0(A_16,B_17),B_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_220])).

tff(c_1629,plain,(
    ! [A_109] : k4_xboole_0(A_109,A_109) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1592,c_228])).

tff(c_14,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_200,plain,(
    ! [B_8] : k3_xboole_0(B_8,B_8) = B_8 ),
    inference(resolution,[status(thm)],[c_14,c_188])).

tff(c_250,plain,(
    ! [A_60,B_61] : k5_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_266,plain,(
    ! [B_8] : k5_xboole_0(B_8,B_8) = k4_xboole_0(B_8,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_250])).

tff(c_1692,plain,(
    ! [B_8] : k5_xboole_0(B_8,B_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1629,c_266])).

tff(c_38,plain,(
    ! [A_33,B_34] : r1_tarski(k1_tarski(A_33),k2_tarski(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_198,plain,(
    ! [A_33,B_34] : k3_xboole_0(k1_tarski(A_33),k2_tarski(A_33,B_34)) = k1_tarski(A_33) ),
    inference(resolution,[status(thm)],[c_38,c_188])).

tff(c_16,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_513,plain,(
    ! [A_78,B_79,C_80] : k5_xboole_0(k5_xboole_0(A_78,B_79),C_80) = k5_xboole_0(A_78,k5_xboole_0(B_79,C_80)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2225,plain,(
    ! [C_125,A_126,B_127] : k5_xboole_0(C_125,k5_xboole_0(A_126,B_127)) = k5_xboole_0(A_126,k5_xboole_0(B_127,C_125)) ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_4])).

tff(c_3390,plain,(
    ! [A_148,C_149] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_148,C_149)) = k5_xboole_0(C_149,A_148) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_2225])).

tff(c_3495,plain,(
    ! [A_9,B_10] : k5_xboole_0(k3_xboole_0(A_9,B_10),A_9) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3390])).

tff(c_3704,plain,(
    ! [A_154,B_155] : k5_xboole_0(k3_xboole_0(A_154,B_155),A_154) = k4_xboole_0(A_154,B_155) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_3495])).

tff(c_3778,plain,(
    ! [A_33,B_34] : k5_xboole_0(k1_tarski(A_33),k1_tarski(A_33)) = k4_xboole_0(k1_tarski(A_33),k2_tarski(A_33,B_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_3704])).

tff(c_3817,plain,(
    ! [A_33,B_34] : k4_xboole_0(k1_tarski(A_33),k2_tarski(A_33,B_34)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1692,c_3778])).

tff(c_28,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_269,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_250])).

tff(c_3486,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_3390])).

tff(c_3535,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k4_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_3486])).

tff(c_4022,plain,(
    ! [A_160,B_161,C_162] : k5_xboole_0(A_160,k5_xboole_0(k3_xboole_0(A_160,B_161),C_162)) = k5_xboole_0(k4_xboole_0(A_160,B_161),C_162) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_513])).

tff(c_4089,plain,(
    ! [B_2,A_1] : k5_xboole_0(k4_xboole_0(B_2,A_1),A_1) = k5_xboole_0(B_2,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3535,c_4022])).

tff(c_5648,plain,(
    ! [B_184,A_185] : k5_xboole_0(k4_xboole_0(B_184,A_185),A_185) = k2_xboole_0(B_184,A_185) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4089])).

tff(c_5717,plain,(
    ! [A_33,B_34] : k2_xboole_0(k1_tarski(A_33),k2_tarski(A_33,B_34)) = k5_xboole_0(k1_xboole_0,k2_tarski(A_33,B_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3817,c_5648])).

tff(c_5764,plain,(
    ! [A_33,B_34] : k2_xboole_0(k1_tarski(A_33),k2_tarski(A_33,B_34)) = k2_tarski(A_33,B_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_5717])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24026,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5764,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.68/4.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.68/4.88  
% 10.68/4.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.68/4.88  %$ r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 10.68/4.88  
% 10.68/4.88  %Foreground sorts:
% 10.68/4.88  
% 10.68/4.88  
% 10.68/4.88  %Background operators:
% 10.68/4.88  
% 10.68/4.88  
% 10.68/4.88  %Foreground operators:
% 10.68/4.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.68/4.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.68/4.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.68/4.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.68/4.88  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.68/4.88  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.68/4.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.68/4.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.68/4.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.68/4.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.68/4.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.68/4.88  tff('#skF_2', type, '#skF_2': $i).
% 10.68/4.88  tff('#skF_1', type, '#skF_1': $i).
% 10.68/4.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.68/4.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.68/4.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.68/4.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.68/4.88  
% 10.84/4.90  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 10.84/4.90  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 10.84/4.90  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.84/4.90  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.84/4.90  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 10.84/4.90  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 10.84/4.90  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.84/4.90  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.84/4.90  tff(f_65, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 10.84/4.90  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.84/4.90  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.84/4.90  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.84/4.90  tff(f_68, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 10.84/4.90  tff(c_63, plain, (![B_42, A_43]: (k5_xboole_0(B_42, A_43)=k5_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.84/4.90  tff(c_22, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.84/4.90  tff(c_79, plain, (![A_43]: (k5_xboole_0(k1_xboole_0, A_43)=A_43)), inference(superposition, [status(thm), theory('equality')], [c_63, c_22])).
% 10.84/4.90  tff(c_20, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.84/4.90  tff(c_188, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=A_49 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.84/4.90  tff(c_1592, plain, (![A_109, B_110]: (k3_xboole_0(k4_xboole_0(A_109, B_110), A_109)=k4_xboole_0(A_109, B_110))), inference(resolution, [status(thm)], [c_20, c_188])).
% 10.84/4.90  tff(c_24, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.84/4.90  tff(c_220, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=k1_xboole_0 | ~r1_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.84/4.90  tff(c_228, plain, (![A_16, B_17]: (k3_xboole_0(k4_xboole_0(A_16, B_17), B_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_220])).
% 10.84/4.90  tff(c_1629, plain, (![A_109]: (k4_xboole_0(A_109, A_109)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1592, c_228])).
% 10.84/4.90  tff(c_14, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.84/4.90  tff(c_200, plain, (![B_8]: (k3_xboole_0(B_8, B_8)=B_8)), inference(resolution, [status(thm)], [c_14, c_188])).
% 10.84/4.90  tff(c_250, plain, (![A_60, B_61]: (k5_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.84/4.90  tff(c_266, plain, (![B_8]: (k5_xboole_0(B_8, B_8)=k4_xboole_0(B_8, B_8))), inference(superposition, [status(thm), theory('equality')], [c_200, c_250])).
% 10.84/4.90  tff(c_1692, plain, (![B_8]: (k5_xboole_0(B_8, B_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1629, c_266])).
% 10.84/4.90  tff(c_38, plain, (![A_33, B_34]: (r1_tarski(k1_tarski(A_33), k2_tarski(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.84/4.90  tff(c_198, plain, (![A_33, B_34]: (k3_xboole_0(k1_tarski(A_33), k2_tarski(A_33, B_34))=k1_tarski(A_33))), inference(resolution, [status(thm)], [c_38, c_188])).
% 10.84/4.90  tff(c_16, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.84/4.90  tff(c_513, plain, (![A_78, B_79, C_80]: (k5_xboole_0(k5_xboole_0(A_78, B_79), C_80)=k5_xboole_0(A_78, k5_xboole_0(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.84/4.90  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.84/4.90  tff(c_2225, plain, (![C_125, A_126, B_127]: (k5_xboole_0(C_125, k5_xboole_0(A_126, B_127))=k5_xboole_0(A_126, k5_xboole_0(B_127, C_125)))), inference(superposition, [status(thm), theory('equality')], [c_513, c_4])).
% 10.84/4.90  tff(c_3390, plain, (![A_148, C_149]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_148, C_149))=k5_xboole_0(C_149, A_148))), inference(superposition, [status(thm), theory('equality')], [c_79, c_2225])).
% 10.84/4.90  tff(c_3495, plain, (![A_9, B_10]: (k5_xboole_0(k3_xboole_0(A_9, B_10), A_9)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3390])).
% 10.84/4.90  tff(c_3704, plain, (![A_154, B_155]: (k5_xboole_0(k3_xboole_0(A_154, B_155), A_154)=k4_xboole_0(A_154, B_155))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_3495])).
% 10.84/4.90  tff(c_3778, plain, (![A_33, B_34]: (k5_xboole_0(k1_tarski(A_33), k1_tarski(A_33))=k4_xboole_0(k1_tarski(A_33), k2_tarski(A_33, B_34)))), inference(superposition, [status(thm), theory('equality')], [c_198, c_3704])).
% 10.84/4.90  tff(c_3817, plain, (![A_33, B_34]: (k4_xboole_0(k1_tarski(A_33), k2_tarski(A_33, B_34))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1692, c_3778])).
% 10.84/4.90  tff(c_28, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.84/4.90  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.84/4.90  tff(c_269, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_250])).
% 10.84/4.90  tff(c_3486, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_269, c_3390])).
% 10.84/4.90  tff(c_3535, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k4_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_3486])).
% 10.84/4.90  tff(c_4022, plain, (![A_160, B_161, C_162]: (k5_xboole_0(A_160, k5_xboole_0(k3_xboole_0(A_160, B_161), C_162))=k5_xboole_0(k4_xboole_0(A_160, B_161), C_162))), inference(superposition, [status(thm), theory('equality')], [c_16, c_513])).
% 10.84/4.90  tff(c_4089, plain, (![B_2, A_1]: (k5_xboole_0(k4_xboole_0(B_2, A_1), A_1)=k5_xboole_0(B_2, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_3535, c_4022])).
% 10.84/4.90  tff(c_5648, plain, (![B_184, A_185]: (k5_xboole_0(k4_xboole_0(B_184, A_185), A_185)=k2_xboole_0(B_184, A_185))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4089])).
% 10.84/4.90  tff(c_5717, plain, (![A_33, B_34]: (k2_xboole_0(k1_tarski(A_33), k2_tarski(A_33, B_34))=k5_xboole_0(k1_xboole_0, k2_tarski(A_33, B_34)))), inference(superposition, [status(thm), theory('equality')], [c_3817, c_5648])).
% 10.84/4.90  tff(c_5764, plain, (![A_33, B_34]: (k2_xboole_0(k1_tarski(A_33), k2_tarski(A_33, B_34))=k2_tarski(A_33, B_34))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_5717])).
% 10.84/4.90  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.84/4.90  tff(c_24026, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5764, c_40])).
% 10.84/4.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.84/4.90  
% 10.84/4.90  Inference rules
% 10.84/4.90  ----------------------
% 10.84/4.90  #Ref     : 0
% 10.84/4.90  #Sup     : 5995
% 10.84/4.90  #Fact    : 0
% 10.84/4.90  #Define  : 0
% 10.84/4.90  #Split   : 0
% 10.84/4.90  #Chain   : 0
% 10.84/4.90  #Close   : 0
% 10.84/4.90  
% 10.84/4.90  Ordering : KBO
% 10.84/4.90  
% 10.84/4.90  Simplification rules
% 10.84/4.90  ----------------------
% 10.84/4.90  #Subsume      : 292
% 10.84/4.90  #Demod        : 7460
% 10.84/4.90  #Tautology    : 3502
% 10.84/4.90  #SimpNegUnit  : 0
% 10.84/4.90  #BackRed      : 17
% 10.84/4.90  
% 10.84/4.90  #Partial instantiations: 0
% 10.84/4.90  #Strategies tried      : 1
% 10.84/4.90  
% 10.84/4.90  Timing (in seconds)
% 10.84/4.90  ----------------------
% 10.86/4.90  Preprocessing        : 0.30
% 10.86/4.90  Parsing              : 0.16
% 10.86/4.90  CNF conversion       : 0.02
% 10.86/4.90  Main loop            : 3.80
% 10.86/4.90  Inferencing          : 0.68
% 10.86/4.90  Reduction            : 2.41
% 10.86/4.90  Demodulation         : 2.21
% 10.86/4.90  BG Simplification    : 0.11
% 10.86/4.90  Subsumption          : 0.46
% 10.86/4.90  Abstraction          : 0.16
% 10.86/4.90  MUC search           : 0.00
% 10.86/4.90  Cooper               : 0.00
% 10.86/4.90  Total                : 4.13
% 10.86/4.90  Index Insertion      : 0.00
% 10.86/4.90  Index Deletion       : 0.00
% 10.86/4.90  Index Matching       : 0.00
% 10.86/4.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
