%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:25 EST 2020

% Result     : Theorem 4.86s
% Output     : CNFRefutation 4.86s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 451 expanded)
%              Number of leaves         :   32 ( 165 expanded)
%              Depth                    :   15
%              Number of atoms          :   74 ( 486 expanded)
%              Number of equality atoms :   64 ( 464 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_48,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_546,plain,(
    ! [A_97,B_98] : k5_xboole_0(A_97,k3_xboole_0(A_97,B_98)) = k4_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_567,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_546])).

tff(c_572,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_567])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_50,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_75,plain,(
    ! [A_58,B_59] : r1_tarski(A_58,k2_xboole_0(A_58,B_59)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_78,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_75])).

tff(c_601,plain,(
    ! [B_103,A_104] :
      ( k1_tarski(B_103) = A_104
      | k1_xboole_0 = A_104
      | ~ r1_tarski(A_104,k1_tarski(B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_622,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_78,c_601])).

tff(c_634,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_622])).

tff(c_644,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_50])).

tff(c_20,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_723,plain,(
    ! [A_106,B_107,C_108] : k5_xboole_0(k5_xboole_0(A_106,B_107),C_108) = k5_xboole_0(A_106,k5_xboole_0(B_107,C_108)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3521,plain,(
    ! [A_7927,B_7928,C_7929] : k5_xboole_0(A_7927,k5_xboole_0(k4_xboole_0(B_7928,A_7927),C_7929)) = k5_xboole_0(k2_xboole_0(A_7927,B_7928),C_7929) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_723])).

tff(c_3621,plain,(
    ! [A_7927,B_7928] : k5_xboole_0(k2_xboole_0(A_7927,B_7928),k4_xboole_0(B_7928,A_7927)) = k5_xboole_0(A_7927,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_3521])).

tff(c_3650,plain,(
    ! [A_7930,B_7931] : k5_xboole_0(k2_xboole_0(A_7930,B_7931),k4_xboole_0(B_7931,A_7930)) = A_7930 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3621])).

tff(c_3692,plain,(
    k5_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_3650])).

tff(c_1398,plain,(
    ! [A_127,C_128] : k5_xboole_0(A_127,k5_xboole_0(A_127,C_128)) = k5_xboole_0(k1_xboole_0,C_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_723])).

tff(c_1485,plain,(
    ! [A_5] : k5_xboole_0(k1_xboole_0,A_5) = k5_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_1398])).

tff(c_1517,plain,(
    ! [A_5] : k5_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1485])).

tff(c_754,plain,(
    ! [A_5,C_108] : k5_xboole_0(A_5,k5_xboole_0(A_5,C_108)) = k5_xboole_0(k1_xboole_0,C_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_723])).

tff(c_1519,plain,(
    ! [A_5,C_108] : k5_xboole_0(A_5,k5_xboole_0(A_5,C_108)) = C_108 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1517,c_754])).

tff(c_3822,plain,(
    k5_xboole_0('#skF_2','#skF_2') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3692,c_1519])).

tff(c_3836,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_3822])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2579,plain,(
    ! [A_165,B_166,C_167] : k5_xboole_0(A_165,k5_xboole_0(k3_xboole_0(A_165,B_166),C_167)) = k5_xboole_0(k4_xboole_0(A_165,B_166),C_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_723])).

tff(c_2674,plain,(
    ! [A_165,B_166] : k5_xboole_0(k4_xboole_0(A_165,B_166),k3_xboole_0(A_165,B_166)) = k5_xboole_0(A_165,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_2579])).

tff(c_2710,plain,(
    ! [A_165,B_166] : k5_xboole_0(k4_xboole_0(A_165,B_166),k3_xboole_0(A_165,B_166)) = A_165 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2674])).

tff(c_3851,plain,(
    k5_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_3836,c_2710])).

tff(c_758,plain,(
    ! [A_106,B_107] : k5_xboole_0(A_106,k5_xboole_0(B_107,k5_xboole_0(A_106,B_107))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_723])).

tff(c_1601,plain,(
    ! [A_130,C_131] : k5_xboole_0(A_130,k5_xboole_0(A_130,C_131)) = C_131 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1517,c_754])).

tff(c_1645,plain,(
    ! [B_107,A_106] : k5_xboole_0(B_107,k5_xboole_0(A_106,B_107)) = k5_xboole_0(A_106,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_758,c_1601])).

tff(c_1731,plain,(
    ! [B_138,A_139] : k5_xboole_0(B_138,k5_xboole_0(A_139,B_138)) = A_139 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1645])).

tff(c_1684,plain,(
    ! [B_107,A_106] : k5_xboole_0(B_107,k5_xboole_0(A_106,B_107)) = A_106 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1645])).

tff(c_1734,plain,(
    ! [A_139,B_138] : k5_xboole_0(k5_xboole_0(A_139,B_138),A_139) = B_138 ),
    inference(superposition,[status(thm),theory(equality)],[c_1731,c_1684])).

tff(c_4284,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3851,c_1734])).

tff(c_4307,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_4284])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_304,plain,(
    ! [A_77,B_78,C_79] : r1_tarski(k3_xboole_0(A_77,B_78),k2_xboole_0(A_77,C_79)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_338,plain,(
    ! [B_80] : r1_tarski(k3_xboole_0('#skF_2',B_80),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_304])).

tff(c_350,plain,(
    ! [A_1] : r1_tarski(k3_xboole_0(A_1,'#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_338])).

tff(c_626,plain,(
    ! [A_1] :
      ( k3_xboole_0(A_1,'#skF_2') = k1_tarski('#skF_1')
      | k3_xboole_0(A_1,'#skF_2') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_350,c_601])).

tff(c_1303,plain,(
    ! [A_1] :
      ( k3_xboole_0(A_1,'#skF_2') = '#skF_2'
      | k3_xboole_0(A_1,'#skF_2') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_626])).

tff(c_4324,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4307,c_1303])).

tff(c_4357,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4307,c_4324])).

tff(c_4359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_48,c_4357])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:51:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.86/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/1.96  
% 4.86/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/1.96  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.86/1.96  
% 4.86/1.96  %Foreground sorts:
% 4.86/1.96  
% 4.86/1.96  
% 4.86/1.96  %Background operators:
% 4.86/1.96  
% 4.86/1.96  
% 4.86/1.96  %Foreground operators:
% 4.86/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.86/1.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.86/1.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.86/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.86/1.96  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.86/1.96  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.86/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.86/1.96  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.86/1.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.86/1.96  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.86/1.96  tff('#skF_2', type, '#skF_2': $i).
% 4.86/1.96  tff('#skF_3', type, '#skF_3': $i).
% 4.86/1.96  tff('#skF_1', type, '#skF_1': $i).
% 4.86/1.96  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.86/1.96  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.86/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.86/1.96  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.86/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.86/1.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.86/1.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.86/1.96  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.86/1.96  
% 4.86/1.98  tff(f_80, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 4.86/1.98  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.86/1.98  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.86/1.98  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 4.86/1.98  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.86/1.98  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.86/1.98  tff(f_65, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.86/1.98  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.86/1.98  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.86/1.98  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.86/1.98  tff(f_35, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_xboole_1)).
% 4.86/1.98  tff(c_44, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.86/1.98  tff(c_48, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.86/1.98  tff(c_14, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.86/1.98  tff(c_12, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.86/1.98  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.86/1.98  tff(c_546, plain, (![A_97, B_98]: (k5_xboole_0(A_97, k3_xboole_0(A_97, B_98))=k4_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.86/1.98  tff(c_567, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_546])).
% 4.86/1.98  tff(c_572, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_567])).
% 4.86/1.98  tff(c_46, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.86/1.98  tff(c_50, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.86/1.98  tff(c_75, plain, (![A_58, B_59]: (r1_tarski(A_58, k2_xboole_0(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.86/1.98  tff(c_78, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_75])).
% 4.86/1.98  tff(c_601, plain, (![B_103, A_104]: (k1_tarski(B_103)=A_104 | k1_xboole_0=A_104 | ~r1_tarski(A_104, k1_tarski(B_103)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.86/1.98  tff(c_622, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_78, c_601])).
% 4.86/1.98  tff(c_634, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_46, c_622])).
% 4.86/1.98  tff(c_644, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_634, c_50])).
% 4.86/1.98  tff(c_20, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.86/1.98  tff(c_723, plain, (![A_106, B_107, C_108]: (k5_xboole_0(k5_xboole_0(A_106, B_107), C_108)=k5_xboole_0(A_106, k5_xboole_0(B_107, C_108)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.86/1.98  tff(c_3521, plain, (![A_7927, B_7928, C_7929]: (k5_xboole_0(A_7927, k5_xboole_0(k4_xboole_0(B_7928, A_7927), C_7929))=k5_xboole_0(k2_xboole_0(A_7927, B_7928), C_7929))), inference(superposition, [status(thm), theory('equality')], [c_20, c_723])).
% 4.86/1.98  tff(c_3621, plain, (![A_7927, B_7928]: (k5_xboole_0(k2_xboole_0(A_7927, B_7928), k4_xboole_0(B_7928, A_7927))=k5_xboole_0(A_7927, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_572, c_3521])).
% 4.86/1.98  tff(c_3650, plain, (![A_7930, B_7931]: (k5_xboole_0(k2_xboole_0(A_7930, B_7931), k4_xboole_0(B_7931, A_7930))=A_7930)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3621])).
% 4.86/1.98  tff(c_3692, plain, (k5_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_644, c_3650])).
% 4.86/1.98  tff(c_1398, plain, (![A_127, C_128]: (k5_xboole_0(A_127, k5_xboole_0(A_127, C_128))=k5_xboole_0(k1_xboole_0, C_128))), inference(superposition, [status(thm), theory('equality')], [c_572, c_723])).
% 4.86/1.98  tff(c_1485, plain, (![A_5]: (k5_xboole_0(k1_xboole_0, A_5)=k5_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_572, c_1398])).
% 4.86/1.98  tff(c_1517, plain, (![A_5]: (k5_xboole_0(k1_xboole_0, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1485])).
% 4.86/1.98  tff(c_754, plain, (![A_5, C_108]: (k5_xboole_0(A_5, k5_xboole_0(A_5, C_108))=k5_xboole_0(k1_xboole_0, C_108))), inference(superposition, [status(thm), theory('equality')], [c_572, c_723])).
% 4.86/1.98  tff(c_1519, plain, (![A_5, C_108]: (k5_xboole_0(A_5, k5_xboole_0(A_5, C_108))=C_108)), inference(demodulation, [status(thm), theory('equality')], [c_1517, c_754])).
% 4.86/1.98  tff(c_3822, plain, (k5_xboole_0('#skF_2', '#skF_2')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3692, c_1519])).
% 4.86/1.98  tff(c_3836, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_572, c_3822])).
% 4.86/1.98  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.86/1.98  tff(c_2579, plain, (![A_165, B_166, C_167]: (k5_xboole_0(A_165, k5_xboole_0(k3_xboole_0(A_165, B_166), C_167))=k5_xboole_0(k4_xboole_0(A_165, B_166), C_167))), inference(superposition, [status(thm), theory('equality')], [c_4, c_723])).
% 4.86/1.98  tff(c_2674, plain, (![A_165, B_166]: (k5_xboole_0(k4_xboole_0(A_165, B_166), k3_xboole_0(A_165, B_166))=k5_xboole_0(A_165, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_572, c_2579])).
% 4.86/1.98  tff(c_2710, plain, (![A_165, B_166]: (k5_xboole_0(k4_xboole_0(A_165, B_166), k3_xboole_0(A_165, B_166))=A_165)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2674])).
% 4.86/1.98  tff(c_3851, plain, (k5_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_3836, c_2710])).
% 4.86/1.98  tff(c_758, plain, (![A_106, B_107]: (k5_xboole_0(A_106, k5_xboole_0(B_107, k5_xboole_0(A_106, B_107)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_572, c_723])).
% 4.86/1.98  tff(c_1601, plain, (![A_130, C_131]: (k5_xboole_0(A_130, k5_xboole_0(A_130, C_131))=C_131)), inference(demodulation, [status(thm), theory('equality')], [c_1517, c_754])).
% 4.86/1.98  tff(c_1645, plain, (![B_107, A_106]: (k5_xboole_0(B_107, k5_xboole_0(A_106, B_107))=k5_xboole_0(A_106, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_758, c_1601])).
% 4.86/1.98  tff(c_1731, plain, (![B_138, A_139]: (k5_xboole_0(B_138, k5_xboole_0(A_139, B_138))=A_139)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1645])).
% 4.86/1.98  tff(c_1684, plain, (![B_107, A_106]: (k5_xboole_0(B_107, k5_xboole_0(A_106, B_107))=A_106)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1645])).
% 4.86/1.98  tff(c_1734, plain, (![A_139, B_138]: (k5_xboole_0(k5_xboole_0(A_139, B_138), A_139)=B_138)), inference(superposition, [status(thm), theory('equality')], [c_1731, c_1684])).
% 4.86/1.98  tff(c_4284, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3851, c_1734])).
% 4.86/1.98  tff(c_4307, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_4284])).
% 4.86/1.98  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.86/1.98  tff(c_304, plain, (![A_77, B_78, C_79]: (r1_tarski(k3_xboole_0(A_77, B_78), k2_xboole_0(A_77, C_79)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.86/1.98  tff(c_338, plain, (![B_80]: (r1_tarski(k3_xboole_0('#skF_2', B_80), k1_tarski('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_50, c_304])).
% 4.86/1.98  tff(c_350, plain, (![A_1]: (r1_tarski(k3_xboole_0(A_1, '#skF_2'), k1_tarski('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_338])).
% 4.86/1.98  tff(c_626, plain, (![A_1]: (k3_xboole_0(A_1, '#skF_2')=k1_tarski('#skF_1') | k3_xboole_0(A_1, '#skF_2')=k1_xboole_0)), inference(resolution, [status(thm)], [c_350, c_601])).
% 4.86/1.98  tff(c_1303, plain, (![A_1]: (k3_xboole_0(A_1, '#skF_2')='#skF_2' | k3_xboole_0(A_1, '#skF_2')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_634, c_626])).
% 4.86/1.98  tff(c_4324, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4307, c_1303])).
% 4.86/1.98  tff(c_4357, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4307, c_4324])).
% 4.86/1.98  tff(c_4359, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_48, c_4357])).
% 4.86/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/1.98  
% 4.86/1.98  Inference rules
% 4.86/1.98  ----------------------
% 4.86/1.98  #Ref     : 0
% 4.86/1.98  #Sup     : 1164
% 4.86/1.98  #Fact    : 3
% 4.86/1.98  #Define  : 0
% 4.86/1.98  #Split   : 2
% 4.86/1.98  #Chain   : 0
% 4.86/1.98  #Close   : 0
% 4.86/1.98  
% 4.86/1.98  Ordering : KBO
% 4.86/1.98  
% 4.86/1.98  Simplification rules
% 4.86/1.98  ----------------------
% 4.86/1.98  #Subsume      : 124
% 4.86/1.98  #Demod        : 726
% 4.86/1.98  #Tautology    : 590
% 4.86/1.98  #SimpNegUnit  : 34
% 4.86/1.98  #BackRed      : 18
% 4.86/1.98  
% 4.86/1.98  #Partial instantiations: 513
% 4.86/1.98  #Strategies tried      : 1
% 4.86/1.98  
% 4.86/1.98  Timing (in seconds)
% 4.86/1.98  ----------------------
% 4.86/1.98  Preprocessing        : 0.31
% 4.86/1.98  Parsing              : 0.17
% 4.86/1.98  CNF conversion       : 0.02
% 4.86/1.98  Main loop            : 0.87
% 4.86/1.98  Inferencing          : 0.33
% 4.86/1.98  Reduction            : 0.34
% 4.86/1.98  Demodulation         : 0.27
% 4.86/1.98  BG Simplification    : 0.03
% 4.86/1.98  Subsumption          : 0.12
% 4.86/1.98  Abstraction          : 0.04
% 4.86/1.98  MUC search           : 0.00
% 4.86/1.98  Cooper               : 0.00
% 4.86/1.98  Total                : 1.22
% 4.86/1.98  Index Insertion      : 0.00
% 4.86/1.98  Index Deletion       : 0.00
% 4.86/1.98  Index Matching       : 0.00
% 4.86/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
