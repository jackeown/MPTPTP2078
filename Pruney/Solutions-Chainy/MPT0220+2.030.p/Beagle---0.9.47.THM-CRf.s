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
% DateTime   : Thu Dec  3 09:48:07 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 146 expanded)
%              Number of leaves         :   30 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :   48 ( 129 expanded)
%              Number of equality atoms :   43 ( 124 expanded)
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

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_370,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k4_xboole_0(B_81,A_80)) = k2_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_395,plain,(
    ! [A_82] : k5_xboole_0(k1_xboole_0,A_82) = k2_xboole_0(k1_xboole_0,A_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_370])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_410,plain,(
    ! [B_8] : k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,B_8)) = k4_xboole_0(k1_xboole_0,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_8])).

tff(c_448,plain,(
    ! [B_83] : k4_xboole_0(k1_xboole_0,B_83) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_410])).

tff(c_22,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_453,plain,(
    ! [B_83] : k5_xboole_0(B_83,k1_xboole_0) = k2_xboole_0(B_83,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_22])).

tff(c_649,plain,(
    ! [B_91] : k5_xboole_0(B_91,k1_xboole_0) = B_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_453])).

tff(c_696,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_649])).

tff(c_572,plain,(
    ! [A_88,B_89,C_90] : k5_xboole_0(k5_xboole_0(A_88,B_89),C_90) = k5_xboole_0(A_88,k5_xboole_0(B_89,C_90)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2172,plain,(
    ! [A_150,A_148,B_149] : k5_xboole_0(A_150,k5_xboole_0(A_148,B_149)) = k5_xboole_0(A_148,k5_xboole_0(B_149,A_150)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_572])).

tff(c_2548,plain,(
    ! [B_151,A_152] : k5_xboole_0(k1_xboole_0,k5_xboole_0(B_151,A_152)) = k5_xboole_0(A_152,B_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_696,c_2172])).

tff(c_2662,plain,(
    ! [B_21,A_20] : k5_xboole_0(k4_xboole_0(B_21,A_20),A_20) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2548])).

tff(c_2700,plain,(
    ! [B_21,A_20] : k5_xboole_0(k4_xboole_0(B_21,A_20),A_20) = k2_xboole_0(A_20,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_2662])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_341,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_350,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_341])).

tff(c_2644,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_2548])).

tff(c_2696,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k4_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_2644])).

tff(c_6722,plain,(
    ! [A_218,B_219,C_220] : k5_xboole_0(A_218,k5_xboole_0(k3_xboole_0(A_218,B_219),C_220)) = k5_xboole_0(k4_xboole_0(A_218,B_219),C_220) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_572])).

tff(c_6840,plain,(
    ! [B_2,A_1] : k5_xboole_0(k4_xboole_0(B_2,A_1),A_1) = k5_xboole_0(B_2,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2696,c_6722])).

tff(c_6957,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2700,c_22,c_6840])).

tff(c_38,plain,(
    ! [A_50,B_51] : r1_tarski(k1_tarski(A_50),k2_tarski(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_217,plain,(
    ! [A_68,B_69] :
      ( k3_xboole_0(A_68,B_69) = A_68
      | ~ r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1007,plain,(
    ! [A_119,B_120] : k3_xboole_0(k1_tarski(A_119),k2_tarski(A_119,B_120)) = k1_tarski(A_119) ),
    inference(resolution,[status(thm)],[c_38,c_217])).

tff(c_146,plain,(
    ! [B_64,A_65] : k3_xboole_0(B_64,A_65) = k3_xboole_0(A_65,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_161,plain,(
    ! [A_65,B_64] : k2_xboole_0(A_65,k3_xboole_0(B_64,A_65)) = A_65 ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_12])).

tff(c_8769,plain,(
    ! [A_239,B_240] : k2_xboole_0(k2_tarski(A_239,B_240),k1_tarski(A_239)) = k2_tarski(A_239,B_240) ),
    inference(superposition,[status(thm),theory(equality)],[c_1007,c_161])).

tff(c_8814,plain,(
    ! [A_239,B_240] : k2_xboole_0(k1_tarski(A_239),k2_tarski(A_239,B_240)) = k2_tarski(A_239,B_240) ),
    inference(superposition,[status(thm),theory(equality)],[c_6957,c_8769])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_13303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8814,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.67/3.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/3.10  
% 7.67/3.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/3.11  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 7.67/3.11  
% 7.67/3.11  %Foreground sorts:
% 7.67/3.11  
% 7.67/3.11  
% 7.67/3.11  %Background operators:
% 7.67/3.11  
% 7.67/3.11  
% 7.67/3.11  %Foreground operators:
% 7.67/3.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.67/3.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.67/3.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.67/3.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.67/3.11  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.67/3.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.67/3.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.67/3.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.67/3.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.67/3.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.67/3.11  tff('#skF_2', type, '#skF_2': $i).
% 7.67/3.11  tff('#skF_1', type, '#skF_1': $i).
% 7.67/3.11  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.67/3.11  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.67/3.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.67/3.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.67/3.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.67/3.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.67/3.11  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.67/3.11  
% 7.67/3.12  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.67/3.12  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 7.67/3.12  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 7.67/3.12  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.67/3.12  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.67/3.12  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.67/3.12  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.67/3.12  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.67/3.12  tff(f_65, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 7.67/3.12  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.67/3.12  tff(f_68, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 7.67/3.12  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.67/3.12  tff(c_10, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.67/3.12  tff(c_12, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k3_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.67/3.12  tff(c_16, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.67/3.12  tff(c_370, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k4_xboole_0(B_81, A_80))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.67/3.12  tff(c_395, plain, (![A_82]: (k5_xboole_0(k1_xboole_0, A_82)=k2_xboole_0(k1_xboole_0, A_82))), inference(superposition, [status(thm), theory('equality')], [c_16, c_370])).
% 7.67/3.12  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.67/3.12  tff(c_410, plain, (![B_8]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, B_8))=k4_xboole_0(k1_xboole_0, B_8))), inference(superposition, [status(thm), theory('equality')], [c_395, c_8])).
% 7.67/3.12  tff(c_448, plain, (![B_83]: (k4_xboole_0(k1_xboole_0, B_83)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_410])).
% 7.67/3.12  tff(c_22, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.67/3.12  tff(c_453, plain, (![B_83]: (k5_xboole_0(B_83, k1_xboole_0)=k2_xboole_0(B_83, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_448, c_22])).
% 7.67/3.12  tff(c_649, plain, (![B_91]: (k5_xboole_0(B_91, k1_xboole_0)=B_91)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_453])).
% 7.67/3.12  tff(c_696, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_649])).
% 7.67/3.12  tff(c_572, plain, (![A_88, B_89, C_90]: (k5_xboole_0(k5_xboole_0(A_88, B_89), C_90)=k5_xboole_0(A_88, k5_xboole_0(B_89, C_90)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.67/3.12  tff(c_2172, plain, (![A_150, A_148, B_149]: (k5_xboole_0(A_150, k5_xboole_0(A_148, B_149))=k5_xboole_0(A_148, k5_xboole_0(B_149, A_150)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_572])).
% 7.67/3.12  tff(c_2548, plain, (![B_151, A_152]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(B_151, A_152))=k5_xboole_0(A_152, B_151))), inference(superposition, [status(thm), theory('equality')], [c_696, c_2172])).
% 7.67/3.12  tff(c_2662, plain, (![B_21, A_20]: (k5_xboole_0(k4_xboole_0(B_21, A_20), A_20)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2548])).
% 7.67/3.12  tff(c_2700, plain, (![B_21, A_20]: (k5_xboole_0(k4_xboole_0(B_21, A_20), A_20)=k2_xboole_0(A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_696, c_2662])).
% 7.67/3.12  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.67/3.12  tff(c_341, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.67/3.12  tff(c_350, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_341])).
% 7.67/3.12  tff(c_2644, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_350, c_2548])).
% 7.67/3.12  tff(c_2696, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k4_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_696, c_2644])).
% 7.67/3.12  tff(c_6722, plain, (![A_218, B_219, C_220]: (k5_xboole_0(A_218, k5_xboole_0(k3_xboole_0(A_218, B_219), C_220))=k5_xboole_0(k4_xboole_0(A_218, B_219), C_220))), inference(superposition, [status(thm), theory('equality')], [c_8, c_572])).
% 7.67/3.12  tff(c_6840, plain, (![B_2, A_1]: (k5_xboole_0(k4_xboole_0(B_2, A_1), A_1)=k5_xboole_0(B_2, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2696, c_6722])).
% 7.67/3.12  tff(c_6957, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_2700, c_22, c_6840])).
% 7.67/3.12  tff(c_38, plain, (![A_50, B_51]: (r1_tarski(k1_tarski(A_50), k2_tarski(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.67/3.12  tff(c_217, plain, (![A_68, B_69]: (k3_xboole_0(A_68, B_69)=A_68 | ~r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.67/3.12  tff(c_1007, plain, (![A_119, B_120]: (k3_xboole_0(k1_tarski(A_119), k2_tarski(A_119, B_120))=k1_tarski(A_119))), inference(resolution, [status(thm)], [c_38, c_217])).
% 7.67/3.12  tff(c_146, plain, (![B_64, A_65]: (k3_xboole_0(B_64, A_65)=k3_xboole_0(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.67/3.12  tff(c_161, plain, (![A_65, B_64]: (k2_xboole_0(A_65, k3_xboole_0(B_64, A_65))=A_65)), inference(superposition, [status(thm), theory('equality')], [c_146, c_12])).
% 7.67/3.12  tff(c_8769, plain, (![A_239, B_240]: (k2_xboole_0(k2_tarski(A_239, B_240), k1_tarski(A_239))=k2_tarski(A_239, B_240))), inference(superposition, [status(thm), theory('equality')], [c_1007, c_161])).
% 7.67/3.12  tff(c_8814, plain, (![A_239, B_240]: (k2_xboole_0(k1_tarski(A_239), k2_tarski(A_239, B_240))=k2_tarski(A_239, B_240))), inference(superposition, [status(thm), theory('equality')], [c_6957, c_8769])).
% 7.67/3.12  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.67/3.12  tff(c_13303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8814, c_40])).
% 7.67/3.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/3.12  
% 7.67/3.12  Inference rules
% 7.67/3.12  ----------------------
% 7.67/3.12  #Ref     : 0
% 7.67/3.12  #Sup     : 3299
% 7.67/3.12  #Fact    : 0
% 7.67/3.12  #Define  : 0
% 7.67/3.12  #Split   : 0
% 7.67/3.12  #Chain   : 0
% 7.67/3.12  #Close   : 0
% 7.67/3.12  
% 7.67/3.12  Ordering : KBO
% 7.67/3.12  
% 7.67/3.12  Simplification rules
% 7.67/3.12  ----------------------
% 7.67/3.12  #Subsume      : 184
% 7.67/3.12  #Demod        : 3842
% 7.67/3.12  #Tautology    : 1931
% 7.67/3.12  #SimpNegUnit  : 0
% 7.67/3.12  #BackRed      : 9
% 7.67/3.12  
% 7.67/3.12  #Partial instantiations: 0
% 7.67/3.12  #Strategies tried      : 1
% 7.67/3.12  
% 7.67/3.12  Timing (in seconds)
% 7.67/3.12  ----------------------
% 7.67/3.12  Preprocessing        : 0.31
% 7.67/3.12  Parsing              : 0.17
% 7.67/3.12  CNF conversion       : 0.02
% 7.67/3.12  Main loop            : 1.97
% 7.67/3.12  Inferencing          : 0.44
% 7.67/3.12  Reduction            : 1.16
% 7.67/3.12  Demodulation         : 1.05
% 7.67/3.12  BG Simplification    : 0.06
% 7.67/3.12  Subsumption          : 0.22
% 7.67/3.12  Abstraction          : 0.09
% 7.67/3.12  MUC search           : 0.00
% 7.67/3.12  Cooper               : 0.00
% 7.67/3.12  Total                : 2.30
% 7.67/3.12  Index Insertion      : 0.00
% 7.67/3.12  Index Deletion       : 0.00
% 7.67/3.12  Index Matching       : 0.00
% 7.67/3.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
