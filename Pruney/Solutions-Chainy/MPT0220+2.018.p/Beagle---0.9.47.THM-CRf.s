%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:06 EST 2020

% Result     : Theorem 8.21s
% Output     : CNFRefutation 8.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 292 expanded)
%              Number of leaves         :   31 ( 111 expanded)
%              Depth                    :   18
%              Number of atoms          :   64 ( 291 expanded)
%              Number of equality atoms :   56 ( 266 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_14] : k4_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_283,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k4_xboole_0(B_72,A_71)) = k2_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_295,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = k2_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_283])).

tff(c_299,plain,(
    ! [A_73] : k5_xboole_0(A_73,k1_xboole_0) = A_73 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_295])).

tff(c_315,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_299])).

tff(c_168,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k4_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_195,plain,(
    ! [B_67] : k3_xboole_0(k1_xboole_0,B_67) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_207,plain,(
    ! [B_67] : k3_xboole_0(B_67,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_2])).

tff(c_298,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_295])).

tff(c_370,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k3_xboole_0(A_75,B_76)) = k4_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_387,plain,(
    ! [B_67] : k5_xboole_0(B_67,k1_xboole_0) = k4_xboole_0(B_67,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_370])).

tff(c_407,plain,(
    ! [B_77] : k4_xboole_0(B_77,k1_xboole_0) = B_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_387])).

tff(c_18,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_416,plain,(
    ! [B_77] : k4_xboole_0(B_77,B_77) = k3_xboole_0(B_77,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_18])).

tff(c_430,plain,(
    ! [B_77] : k4_xboole_0(B_77,B_77) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_416])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_141,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_149,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_141])).

tff(c_393,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_370])).

tff(c_524,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_393])).

tff(c_40,plain,(
    ! [A_48,B_49] : r1_tarski(k1_tarski(A_48),k2_tarski(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1104,plain,(
    ! [A_107,B_108] : k3_xboole_0(k1_tarski(A_107),k2_tarski(A_107,B_108)) = k1_tarski(A_107) ),
    inference(resolution,[status(thm)],[c_40,c_141])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1113,plain,(
    ! [A_107,B_108] : k5_xboole_0(k1_tarski(A_107),k1_tarski(A_107)) = k4_xboole_0(k1_tarski(A_107),k2_tarski(A_107,B_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1104,c_12])).

tff(c_1121,plain,(
    ! [A_107,B_108] : k4_xboole_0(k1_tarski(A_107),k2_tarski(A_107,B_108)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_1113])).

tff(c_1032,plain,(
    ! [A_105,B_106] : k5_xboole_0(A_105,k3_xboole_0(B_106,A_105)) = k4_xboole_0(A_105,B_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_370])).

tff(c_554,plain,(
    ! [A_85,B_86,C_87] : k5_xboole_0(k5_xboole_0(A_85,B_86),C_87) = k5_xboole_0(A_85,k5_xboole_0(B_86,C_87)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_591,plain,(
    ! [B_6,C_87] : k5_xboole_0(B_6,k5_xboole_0(B_6,C_87)) = k5_xboole_0(k1_xboole_0,C_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_554])).

tff(c_639,plain,(
    ! [B_6,C_87] : k5_xboole_0(B_6,k5_xboole_0(B_6,C_87)) = C_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_591])).

tff(c_1155,plain,(
    ! [A_117,B_118] : k5_xboole_0(A_117,k4_xboole_0(A_117,B_118)) = k3_xboole_0(B_118,A_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_1032,c_639])).

tff(c_1191,plain,(
    ! [A_107,B_108] : k3_xboole_0(k2_tarski(A_107,B_108),k1_tarski(A_107)) = k5_xboole_0(k1_tarski(A_107),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1121,c_1155])).

tff(c_1221,plain,(
    ! [A_107,B_108] : k3_xboole_0(k2_tarski(A_107,B_108),k1_tarski(A_107)) = k1_tarski(A_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_4,c_1191])).

tff(c_643,plain,(
    ! [B_88,C_89] : k5_xboole_0(B_88,k5_xboole_0(B_88,C_89)) = C_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_591])).

tff(c_711,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k5_xboole_0(B_91,A_90)) = B_91 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_643])).

tff(c_761,plain,(
    ! [A_7,B_8] : k5_xboole_0(k3_xboole_0(A_7,B_8),k4_xboole_0(A_7,B_8)) = A_7 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_711])).

tff(c_1212,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k3_xboole_0(k4_xboole_0(A_12,B_13),A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1155])).

tff(c_1226,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2,c_1212])).

tff(c_181,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,k4_xboole_0(A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_168])).

tff(c_2367,plain,(
    ! [A_155,B_156] : k4_xboole_0(A_155,k3_xboole_0(A_155,B_156)) = k4_xboole_0(A_155,B_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1226,c_181])).

tff(c_24,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2397,plain,(
    ! [A_155,B_156] : k5_xboole_0(k3_xboole_0(A_155,B_156),k4_xboole_0(A_155,B_156)) = k2_xboole_0(k3_xboole_0(A_155,B_156),A_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_2367,c_24])).

tff(c_2454,plain,(
    ! [A_157,B_158] : k2_xboole_0(k3_xboole_0(A_157,B_158),A_157) = A_157 ),
    inference(demodulation,[status(thm),theory(equality)],[c_761,c_2397])).

tff(c_2470,plain,(
    ! [A_107,B_108] : k2_xboole_0(k1_tarski(A_107),k2_tarski(A_107,B_108)) = k2_tarski(A_107,B_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_1221,c_2454])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2470,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.21/3.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.21/3.06  
% 8.21/3.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.21/3.06  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 8.21/3.06  
% 8.21/3.06  %Foreground sorts:
% 8.21/3.06  
% 8.21/3.06  
% 8.21/3.06  %Background operators:
% 8.21/3.06  
% 8.21/3.06  
% 8.21/3.06  %Foreground operators:
% 8.21/3.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.21/3.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.21/3.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.21/3.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.21/3.06  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.21/3.06  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.21/3.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.21/3.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.21/3.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.21/3.06  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.21/3.06  tff('#skF_2', type, '#skF_2': $i).
% 8.21/3.06  tff('#skF_1', type, '#skF_1': $i).
% 8.21/3.06  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.21/3.06  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.21/3.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.21/3.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.21/3.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.21/3.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.21/3.06  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.21/3.06  
% 8.21/3.07  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.21/3.07  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 8.21/3.07  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 8.21/3.07  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.21/3.07  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.21/3.07  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.21/3.07  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.21/3.07  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.21/3.07  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.21/3.07  tff(f_67, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 8.21/3.07  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.21/3.07  tff(f_70, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 8.21/3.07  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.21/3.07  tff(c_14, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.21/3.07  tff(c_20, plain, (![A_14]: (k4_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.21/3.07  tff(c_283, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k4_xboole_0(B_72, A_71))=k2_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.21/3.07  tff(c_295, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=k2_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_283])).
% 8.21/3.07  tff(c_299, plain, (![A_73]: (k5_xboole_0(A_73, k1_xboole_0)=A_73)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_295])).
% 8.21/3.07  tff(c_315, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_299])).
% 8.21/3.07  tff(c_168, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k4_xboole_0(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.21/3.07  tff(c_195, plain, (![B_67]: (k3_xboole_0(k1_xboole_0, B_67)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_168, c_20])).
% 8.21/3.07  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.21/3.07  tff(c_207, plain, (![B_67]: (k3_xboole_0(B_67, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_195, c_2])).
% 8.21/3.07  tff(c_298, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_295])).
% 8.21/3.07  tff(c_370, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k3_xboole_0(A_75, B_76))=k4_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.21/3.07  tff(c_387, plain, (![B_67]: (k5_xboole_0(B_67, k1_xboole_0)=k4_xboole_0(B_67, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_207, c_370])).
% 8.21/3.07  tff(c_407, plain, (![B_77]: (k4_xboole_0(B_77, k1_xboole_0)=B_77)), inference(demodulation, [status(thm), theory('equality')], [c_298, c_387])).
% 8.21/3.07  tff(c_18, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.21/3.07  tff(c_416, plain, (![B_77]: (k4_xboole_0(B_77, B_77)=k3_xboole_0(B_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_407, c_18])).
% 8.21/3.07  tff(c_430, plain, (![B_77]: (k4_xboole_0(B_77, B_77)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_207, c_416])).
% 8.21/3.07  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.21/3.07  tff(c_141, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.21/3.07  tff(c_149, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_141])).
% 8.21/3.07  tff(c_393, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_149, c_370])).
% 8.21/3.07  tff(c_524, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_430, c_393])).
% 8.21/3.07  tff(c_40, plain, (![A_48, B_49]: (r1_tarski(k1_tarski(A_48), k2_tarski(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.21/3.07  tff(c_1104, plain, (![A_107, B_108]: (k3_xboole_0(k1_tarski(A_107), k2_tarski(A_107, B_108))=k1_tarski(A_107))), inference(resolution, [status(thm)], [c_40, c_141])).
% 8.21/3.07  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.21/3.07  tff(c_1113, plain, (![A_107, B_108]: (k5_xboole_0(k1_tarski(A_107), k1_tarski(A_107))=k4_xboole_0(k1_tarski(A_107), k2_tarski(A_107, B_108)))), inference(superposition, [status(thm), theory('equality')], [c_1104, c_12])).
% 8.21/3.07  tff(c_1121, plain, (![A_107, B_108]: (k4_xboole_0(k1_tarski(A_107), k2_tarski(A_107, B_108))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_524, c_1113])).
% 8.21/3.07  tff(c_1032, plain, (![A_105, B_106]: (k5_xboole_0(A_105, k3_xboole_0(B_106, A_105))=k4_xboole_0(A_105, B_106))), inference(superposition, [status(thm), theory('equality')], [c_2, c_370])).
% 8.21/3.07  tff(c_554, plain, (![A_85, B_86, C_87]: (k5_xboole_0(k5_xboole_0(A_85, B_86), C_87)=k5_xboole_0(A_85, k5_xboole_0(B_86, C_87)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.21/3.07  tff(c_591, plain, (![B_6, C_87]: (k5_xboole_0(B_6, k5_xboole_0(B_6, C_87))=k5_xboole_0(k1_xboole_0, C_87))), inference(superposition, [status(thm), theory('equality')], [c_524, c_554])).
% 8.21/3.07  tff(c_639, plain, (![B_6, C_87]: (k5_xboole_0(B_6, k5_xboole_0(B_6, C_87))=C_87)), inference(demodulation, [status(thm), theory('equality')], [c_315, c_591])).
% 8.21/3.07  tff(c_1155, plain, (![A_117, B_118]: (k5_xboole_0(A_117, k4_xboole_0(A_117, B_118))=k3_xboole_0(B_118, A_117))), inference(superposition, [status(thm), theory('equality')], [c_1032, c_639])).
% 8.21/3.07  tff(c_1191, plain, (![A_107, B_108]: (k3_xboole_0(k2_tarski(A_107, B_108), k1_tarski(A_107))=k5_xboole_0(k1_tarski(A_107), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1121, c_1155])).
% 8.21/3.07  tff(c_1221, plain, (![A_107, B_108]: (k3_xboole_0(k2_tarski(A_107, B_108), k1_tarski(A_107))=k1_tarski(A_107))), inference(demodulation, [status(thm), theory('equality')], [c_315, c_4, c_1191])).
% 8.21/3.07  tff(c_643, plain, (![B_88, C_89]: (k5_xboole_0(B_88, k5_xboole_0(B_88, C_89))=C_89)), inference(demodulation, [status(thm), theory('equality')], [c_315, c_591])).
% 8.21/3.07  tff(c_711, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k5_xboole_0(B_91, A_90))=B_91)), inference(superposition, [status(thm), theory('equality')], [c_4, c_643])).
% 8.21/3.07  tff(c_761, plain, (![A_7, B_8]: (k5_xboole_0(k3_xboole_0(A_7, B_8), k4_xboole_0(A_7, B_8))=A_7)), inference(superposition, [status(thm), theory('equality')], [c_12, c_711])).
% 8.21/3.07  tff(c_1212, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k3_xboole_0(k4_xboole_0(A_12, B_13), A_12))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1155])).
% 8.21/3.07  tff(c_1226, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2, c_1212])).
% 8.21/3.07  tff(c_181, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k3_xboole_0(A_12, k4_xboole_0(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_168])).
% 8.21/3.07  tff(c_2367, plain, (![A_155, B_156]: (k4_xboole_0(A_155, k3_xboole_0(A_155, B_156))=k4_xboole_0(A_155, B_156))), inference(demodulation, [status(thm), theory('equality')], [c_1226, c_181])).
% 8.21/3.07  tff(c_24, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.21/3.07  tff(c_2397, plain, (![A_155, B_156]: (k5_xboole_0(k3_xboole_0(A_155, B_156), k4_xboole_0(A_155, B_156))=k2_xboole_0(k3_xboole_0(A_155, B_156), A_155))), inference(superposition, [status(thm), theory('equality')], [c_2367, c_24])).
% 8.21/3.07  tff(c_2454, plain, (![A_157, B_158]: (k2_xboole_0(k3_xboole_0(A_157, B_158), A_157)=A_157)), inference(demodulation, [status(thm), theory('equality')], [c_761, c_2397])).
% 8.21/3.07  tff(c_2470, plain, (![A_107, B_108]: (k2_xboole_0(k1_tarski(A_107), k2_tarski(A_107, B_108))=k2_tarski(A_107, B_108))), inference(superposition, [status(thm), theory('equality')], [c_1221, c_2454])).
% 8.21/3.07  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.21/3.07  tff(c_12737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2470, c_42])).
% 8.21/3.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.21/3.07  
% 8.21/3.07  Inference rules
% 8.21/3.07  ----------------------
% 8.21/3.07  #Ref     : 0
% 8.21/3.07  #Sup     : 3166
% 8.21/3.07  #Fact    : 0
% 8.21/3.07  #Define  : 0
% 8.21/3.07  #Split   : 0
% 8.21/3.07  #Chain   : 0
% 8.21/3.07  #Close   : 0
% 8.21/3.07  
% 8.21/3.07  Ordering : KBO
% 8.21/3.07  
% 8.21/3.07  Simplification rules
% 8.21/3.07  ----------------------
% 8.21/3.07  #Subsume      : 196
% 8.21/3.07  #Demod        : 3690
% 8.21/3.07  #Tautology    : 1836
% 8.21/3.07  #SimpNegUnit  : 0
% 8.21/3.07  #BackRed      : 1
% 8.21/3.07  
% 8.21/3.07  #Partial instantiations: 0
% 8.21/3.07  #Strategies tried      : 1
% 8.21/3.07  
% 8.21/3.07  Timing (in seconds)
% 8.21/3.07  ----------------------
% 8.21/3.08  Preprocessing        : 0.33
% 8.21/3.08  Parsing              : 0.18
% 8.21/3.08  CNF conversion       : 0.02
% 8.21/3.08  Main loop            : 1.95
% 8.21/3.08  Inferencing          : 0.45
% 8.21/3.08  Reduction            : 1.14
% 8.21/3.08  Demodulation         : 1.03
% 8.21/3.08  BG Simplification    : 0.06
% 8.21/3.08  Subsumption          : 0.22
% 8.21/3.08  Abstraction          : 0.11
% 8.21/3.08  MUC search           : 0.00
% 8.21/3.08  Cooper               : 0.00
% 8.21/3.08  Total                : 2.31
% 8.21/3.08  Index Insertion      : 0.00
% 8.21/3.08  Index Deletion       : 0.00
% 8.21/3.08  Index Matching       : 0.00
% 8.21/3.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
