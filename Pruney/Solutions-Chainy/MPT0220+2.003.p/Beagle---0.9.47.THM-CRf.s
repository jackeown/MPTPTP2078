%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:04 EST 2020

% Result     : Theorem 8.88s
% Output     : CNFRefutation 9.12s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 341 expanded)
%              Number of leaves         :   41 ( 133 expanded)
%              Depth                    :   16
%              Number of atoms          :  104 ( 378 expanded)
%              Number of equality atoms :   55 ( 265 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_67,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_83,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_63,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_69,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_55,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_99,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_28,plain,(
    ! [A_23] : k4_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_375,plain,(
    ! [A_100,B_101] : k5_xboole_0(A_100,k4_xboole_0(B_101,A_100)) = k2_xboole_0(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_391,plain,(
    ! [A_103] : k5_xboole_0(k1_xboole_0,A_103) = k2_xboole_0(k1_xboole_0,A_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_375])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_401,plain,(
    ! [A_103] : k5_xboole_0(A_103,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_4])).

tff(c_24,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_167,plain,(
    ! [A_84,B_85] :
      ( k3_xboole_0(A_84,B_85) = A_84
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_202,plain,(
    ! [A_89] : k3_xboole_0(k1_xboole_0,A_89) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_167])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_211,plain,(
    ! [A_89] : k3_xboole_0(A_89,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_2])).

tff(c_472,plain,(
    ! [A_107,B_108] : k5_xboole_0(A_107,k3_xboole_0(A_107,B_108)) = k4_xboole_0(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_489,plain,(
    ! [A_89] : k5_xboole_0(A_89,k1_xboole_0) = k4_xboole_0(A_89,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_472])).

tff(c_506,plain,(
    ! [A_89] : k2_xboole_0(k1_xboole_0,A_89) = A_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_28,c_489])).

tff(c_387,plain,(
    ! [A_23] : k5_xboole_0(k1_xboole_0,A_23) = k2_xboole_0(k1_xboole_0,A_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_375])).

tff(c_525,plain,(
    ! [A_23] : k5_xboole_0(k1_xboole_0,A_23) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_387])).

tff(c_26,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1368,plain,(
    ! [A_175,B_176] : k3_xboole_0(k4_xboole_0(A_175,B_176),A_175) = k4_xboole_0(A_175,B_176) ),
    inference(resolution,[status(thm)],[c_26,c_167])).

tff(c_32,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_xboole_0(A_5)
      | r2_hidden('#skF_1'(A_5),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_276,plain,(
    ! [A_91,B_92,C_93] :
      ( ~ r1_xboole_0(A_91,B_92)
      | ~ r2_hidden(C_93,k3_xboole_0(A_91,B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_787,plain,(
    ! [A_122,B_123] :
      ( ~ r1_xboole_0(A_122,B_123)
      | v1_xboole_0(k3_xboole_0(A_122,B_123)) ) ),
    inference(resolution,[status(thm)],[c_8,c_276])).

tff(c_877,plain,(
    ! [B_137,A_138] :
      ( ~ r1_xboole_0(B_137,A_138)
      | v1_xboole_0(k3_xboole_0(A_138,B_137)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_787])).

tff(c_697,plain,(
    ! [A_118,B_119] :
      ( r2_hidden('#skF_2'(A_118,B_119),k3_xboole_0(A_118,B_119))
      | r1_xboole_0(A_118,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [B_8,A_5] :
      ( ~ r2_hidden(B_8,A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_720,plain,(
    ! [A_118,B_119] :
      ( ~ v1_xboole_0(k3_xboole_0(A_118,B_119))
      | r1_xboole_0(A_118,B_119) ) ),
    inference(resolution,[status(thm)],[c_697,c_6])).

tff(c_908,plain,(
    ! [A_139,B_140] :
      ( r1_xboole_0(A_139,B_140)
      | ~ r1_xboole_0(B_140,A_139) ) ),
    inference(resolution,[status(thm)],[c_877,c_720])).

tff(c_920,plain,(
    ! [B_26,A_25] : r1_xboole_0(B_26,k4_xboole_0(A_25,B_26)) ),
    inference(resolution,[status(thm)],[c_32,c_908])).

tff(c_30,plain,(
    ! [A_24] : r1_xboole_0(A_24,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_279,plain,(
    ! [A_89,C_93] :
      ( ~ r1_xboole_0(A_89,k1_xboole_0)
      | ~ r2_hidden(C_93,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_276])).

tff(c_299,plain,(
    ! [C_94] : ~ r2_hidden(C_94,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_279])).

tff(c_304,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_299])).

tff(c_34,plain,(
    ! [B_28,A_27] :
      ( ~ v1_xboole_0(B_28)
      | B_28 = A_27
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_307,plain,(
    ! [A_27] :
      ( k1_xboole_0 = A_27
      | ~ v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_304,c_34])).

tff(c_973,plain,(
    ! [A_151,B_152] :
      ( k3_xboole_0(A_151,B_152) = k1_xboole_0
      | ~ r1_xboole_0(B_152,A_151) ) ),
    inference(resolution,[status(thm)],[c_877,c_307])).

tff(c_989,plain,(
    ! [A_25,B_26] : k3_xboole_0(k4_xboole_0(A_25,B_26),B_26) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_920,c_973])).

tff(c_1381,plain,(
    ! [A_175] : k4_xboole_0(A_175,A_175) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1368,c_989])).

tff(c_18,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_182,plain,(
    ! [B_15] : k3_xboole_0(B_15,B_15) = B_15 ),
    inference(resolution,[status(thm)],[c_18,c_167])).

tff(c_495,plain,(
    ! [B_15] : k5_xboole_0(B_15,B_15) = k4_xboole_0(B_15,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_472])).

tff(c_1448,plain,(
    ! [B_15] : k5_xboole_0(B_15,B_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1381,c_495])).

tff(c_54,plain,(
    ! [A_62,B_63] : r1_tarski(k1_tarski(A_62),k2_tarski(A_62,B_63)) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_180,plain,(
    ! [A_62,B_63] : k3_xboole_0(k1_tarski(A_62),k2_tarski(A_62,B_63)) = k1_tarski(A_62) ),
    inference(resolution,[status(thm)],[c_54,c_167])).

tff(c_20,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_617,plain,(
    ! [A_115,B_116,C_117] : k5_xboole_0(k5_xboole_0(A_115,B_116),C_117) = k5_xboole_0(A_115,k5_xboole_0(B_116,C_117)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2308,plain,(
    ! [B_199,A_200,B_201] : k5_xboole_0(B_199,k5_xboole_0(A_200,B_201)) = k5_xboole_0(A_200,k5_xboole_0(B_201,B_199)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_617])).

tff(c_2646,plain,(
    ! [A_202,B_203] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_202,B_203)) = k5_xboole_0(B_203,A_202) ),
    inference(superposition,[status(thm),theory(equality)],[c_525,c_2308])).

tff(c_2751,plain,(
    ! [A_16,B_17] : k5_xboole_0(k3_xboole_0(A_16,B_17),A_16) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2646])).

tff(c_2907,plain,(
    ! [A_206,B_207] : k5_xboole_0(k3_xboole_0(A_206,B_207),A_206) = k4_xboole_0(A_206,B_207) ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_2751])).

tff(c_2980,plain,(
    ! [A_62,B_63] : k5_xboole_0(k1_tarski(A_62),k1_tarski(A_62)) = k4_xboole_0(k1_tarski(A_62),k2_tarski(A_62,B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_2907])).

tff(c_3037,plain,(
    ! [A_208,B_209] : k4_xboole_0(k1_tarski(A_208),k2_tarski(A_208,B_209)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_2980])).

tff(c_38,plain,(
    ! [A_32,B_33] : k5_xboole_0(A_32,k4_xboole_0(B_33,A_32)) = k2_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3072,plain,(
    ! [A_208,B_209] : k2_xboole_0(k2_tarski(A_208,B_209),k1_tarski(A_208)) = k5_xboole_0(k2_tarski(A_208,B_209),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3037,c_38])).

tff(c_18516,plain,(
    ! [A_402,B_403] : k2_xboole_0(k2_tarski(A_402,B_403),k1_tarski(A_402)) = k2_tarski(A_402,B_403) ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_4,c_3072])).

tff(c_2754,plain,(
    ! [B_33,A_32] : k5_xboole_0(k4_xboole_0(B_33,A_32),A_32) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_32,B_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2646])).

tff(c_2788,plain,(
    ! [B_33,A_32] : k5_xboole_0(k4_xboole_0(B_33,A_32),A_32) = k2_xboole_0(A_32,B_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_2754])).

tff(c_501,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_472])).

tff(c_2736,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_2646])).

tff(c_2784,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k4_xboole_0(B_2,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_2736])).

tff(c_6122,plain,(
    ! [A_262,B_263,C_264] : k5_xboole_0(A_262,k5_xboole_0(k3_xboole_0(A_262,B_263),C_264)) = k5_xboole_0(k4_xboole_0(A_262,B_263),C_264) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_617])).

tff(c_6232,plain,(
    ! [A_1,B_2] : k5_xboole_0(k4_xboole_0(A_1,B_2),B_2) = k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2784,c_6122])).

tff(c_6345,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2788,c_38,c_6232])).

tff(c_18546,plain,(
    ! [A_402,B_403] : k2_xboole_0(k1_tarski(A_402),k2_tarski(A_402,B_403)) = k2_tarski(A_402,B_403) ),
    inference(superposition,[status(thm),theory(equality)],[c_18516,c_6345])).

tff(c_56,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_3','#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_18692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18546,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:22:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.88/3.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.88/3.63  
% 8.88/3.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.88/3.63  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 8.88/3.63  
% 8.88/3.63  %Foreground sorts:
% 8.88/3.63  
% 8.88/3.63  
% 8.88/3.63  %Background operators:
% 8.88/3.63  
% 8.88/3.63  
% 8.88/3.63  %Foreground operators:
% 8.88/3.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.88/3.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.88/3.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.88/3.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.88/3.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.88/3.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.88/3.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.88/3.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.88/3.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.88/3.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.88/3.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.88/3.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.88/3.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.88/3.63  tff('#skF_3', type, '#skF_3': $i).
% 8.88/3.63  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.88/3.63  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.88/3.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.88/3.63  tff('#skF_4', type, '#skF_4': $i).
% 8.88/3.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.88/3.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.88/3.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.88/3.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.88/3.63  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.88/3.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.88/3.63  
% 9.12/3.65  tff(f_67, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.12/3.65  tff(f_83, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.12/3.65  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 9.12/3.65  tff(f_63, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.12/3.65  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.12/3.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.12/3.65  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.12/3.65  tff(f_65, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.12/3.65  tff(f_71, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 9.12/3.65  tff(f_35, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.12/3.65  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 9.12/3.65  tff(f_69, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 9.12/3.65  tff(f_79, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 9.12/3.65  tff(f_55, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.12/3.65  tff(f_99, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 9.12/3.65  tff(f_81, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.12/3.65  tff(f_102, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 9.12/3.65  tff(c_28, plain, (![A_23]: (k4_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.12/3.65  tff(c_375, plain, (![A_100, B_101]: (k5_xboole_0(A_100, k4_xboole_0(B_101, A_100))=k2_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.12/3.65  tff(c_391, plain, (![A_103]: (k5_xboole_0(k1_xboole_0, A_103)=k2_xboole_0(k1_xboole_0, A_103))), inference(superposition, [status(thm), theory('equality')], [c_28, c_375])).
% 9.12/3.65  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.12/3.65  tff(c_401, plain, (![A_103]: (k5_xboole_0(A_103, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_103))), inference(superposition, [status(thm), theory('equality')], [c_391, c_4])).
% 9.12/3.65  tff(c_24, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.12/3.65  tff(c_167, plain, (![A_84, B_85]: (k3_xboole_0(A_84, B_85)=A_84 | ~r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.12/3.65  tff(c_202, plain, (![A_89]: (k3_xboole_0(k1_xboole_0, A_89)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_167])).
% 9.12/3.65  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.12/3.65  tff(c_211, plain, (![A_89]: (k3_xboole_0(A_89, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_202, c_2])).
% 9.12/3.65  tff(c_472, plain, (![A_107, B_108]: (k5_xboole_0(A_107, k3_xboole_0(A_107, B_108))=k4_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.12/3.65  tff(c_489, plain, (![A_89]: (k5_xboole_0(A_89, k1_xboole_0)=k4_xboole_0(A_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_211, c_472])).
% 9.12/3.65  tff(c_506, plain, (![A_89]: (k2_xboole_0(k1_xboole_0, A_89)=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_401, c_28, c_489])).
% 9.12/3.65  tff(c_387, plain, (![A_23]: (k5_xboole_0(k1_xboole_0, A_23)=k2_xboole_0(k1_xboole_0, A_23))), inference(superposition, [status(thm), theory('equality')], [c_28, c_375])).
% 9.12/3.65  tff(c_525, plain, (![A_23]: (k5_xboole_0(k1_xboole_0, A_23)=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_506, c_387])).
% 9.12/3.65  tff(c_26, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.12/3.65  tff(c_1368, plain, (![A_175, B_176]: (k3_xboole_0(k4_xboole_0(A_175, B_176), A_175)=k4_xboole_0(A_175, B_176))), inference(resolution, [status(thm)], [c_26, c_167])).
% 9.12/3.65  tff(c_32, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.12/3.65  tff(c_8, plain, (![A_5]: (v1_xboole_0(A_5) | r2_hidden('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.12/3.65  tff(c_276, plain, (![A_91, B_92, C_93]: (~r1_xboole_0(A_91, B_92) | ~r2_hidden(C_93, k3_xboole_0(A_91, B_92)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.12/3.65  tff(c_787, plain, (![A_122, B_123]: (~r1_xboole_0(A_122, B_123) | v1_xboole_0(k3_xboole_0(A_122, B_123)))), inference(resolution, [status(thm)], [c_8, c_276])).
% 9.12/3.65  tff(c_877, plain, (![B_137, A_138]: (~r1_xboole_0(B_137, A_138) | v1_xboole_0(k3_xboole_0(A_138, B_137)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_787])).
% 9.12/3.65  tff(c_697, plain, (![A_118, B_119]: (r2_hidden('#skF_2'(A_118, B_119), k3_xboole_0(A_118, B_119)) | r1_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.12/3.65  tff(c_6, plain, (![B_8, A_5]: (~r2_hidden(B_8, A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.12/3.65  tff(c_720, plain, (![A_118, B_119]: (~v1_xboole_0(k3_xboole_0(A_118, B_119)) | r1_xboole_0(A_118, B_119))), inference(resolution, [status(thm)], [c_697, c_6])).
% 9.12/3.65  tff(c_908, plain, (![A_139, B_140]: (r1_xboole_0(A_139, B_140) | ~r1_xboole_0(B_140, A_139))), inference(resolution, [status(thm)], [c_877, c_720])).
% 9.12/3.65  tff(c_920, plain, (![B_26, A_25]: (r1_xboole_0(B_26, k4_xboole_0(A_25, B_26)))), inference(resolution, [status(thm)], [c_32, c_908])).
% 9.12/3.65  tff(c_30, plain, (![A_24]: (r1_xboole_0(A_24, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.12/3.65  tff(c_279, plain, (![A_89, C_93]: (~r1_xboole_0(A_89, k1_xboole_0) | ~r2_hidden(C_93, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_211, c_276])).
% 9.12/3.65  tff(c_299, plain, (![C_94]: (~r2_hidden(C_94, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_279])).
% 9.12/3.65  tff(c_304, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_299])).
% 9.12/3.65  tff(c_34, plain, (![B_28, A_27]: (~v1_xboole_0(B_28) | B_28=A_27 | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.12/3.65  tff(c_307, plain, (![A_27]: (k1_xboole_0=A_27 | ~v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_304, c_34])).
% 9.12/3.65  tff(c_973, plain, (![A_151, B_152]: (k3_xboole_0(A_151, B_152)=k1_xboole_0 | ~r1_xboole_0(B_152, A_151))), inference(resolution, [status(thm)], [c_877, c_307])).
% 9.12/3.65  tff(c_989, plain, (![A_25, B_26]: (k3_xboole_0(k4_xboole_0(A_25, B_26), B_26)=k1_xboole_0)), inference(resolution, [status(thm)], [c_920, c_973])).
% 9.12/3.65  tff(c_1381, plain, (![A_175]: (k4_xboole_0(A_175, A_175)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1368, c_989])).
% 9.12/3.65  tff(c_18, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.12/3.65  tff(c_182, plain, (![B_15]: (k3_xboole_0(B_15, B_15)=B_15)), inference(resolution, [status(thm)], [c_18, c_167])).
% 9.12/3.65  tff(c_495, plain, (![B_15]: (k5_xboole_0(B_15, B_15)=k4_xboole_0(B_15, B_15))), inference(superposition, [status(thm), theory('equality')], [c_182, c_472])).
% 9.12/3.65  tff(c_1448, plain, (![B_15]: (k5_xboole_0(B_15, B_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1381, c_495])).
% 9.12/3.65  tff(c_54, plain, (![A_62, B_63]: (r1_tarski(k1_tarski(A_62), k2_tarski(A_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.12/3.65  tff(c_180, plain, (![A_62, B_63]: (k3_xboole_0(k1_tarski(A_62), k2_tarski(A_62, B_63))=k1_tarski(A_62))), inference(resolution, [status(thm)], [c_54, c_167])).
% 9.12/3.65  tff(c_20, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.12/3.65  tff(c_617, plain, (![A_115, B_116, C_117]: (k5_xboole_0(k5_xboole_0(A_115, B_116), C_117)=k5_xboole_0(A_115, k5_xboole_0(B_116, C_117)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.12/3.65  tff(c_2308, plain, (![B_199, A_200, B_201]: (k5_xboole_0(B_199, k5_xboole_0(A_200, B_201))=k5_xboole_0(A_200, k5_xboole_0(B_201, B_199)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_617])).
% 9.12/3.65  tff(c_2646, plain, (![A_202, B_203]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_202, B_203))=k5_xboole_0(B_203, A_202))), inference(superposition, [status(thm), theory('equality')], [c_525, c_2308])).
% 9.12/3.65  tff(c_2751, plain, (![A_16, B_17]: (k5_xboole_0(k3_xboole_0(A_16, B_17), A_16)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2646])).
% 9.12/3.65  tff(c_2907, plain, (![A_206, B_207]: (k5_xboole_0(k3_xboole_0(A_206, B_207), A_206)=k4_xboole_0(A_206, B_207))), inference(demodulation, [status(thm), theory('equality')], [c_525, c_2751])).
% 9.12/3.65  tff(c_2980, plain, (![A_62, B_63]: (k5_xboole_0(k1_tarski(A_62), k1_tarski(A_62))=k4_xboole_0(k1_tarski(A_62), k2_tarski(A_62, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_180, c_2907])).
% 9.12/3.65  tff(c_3037, plain, (![A_208, B_209]: (k4_xboole_0(k1_tarski(A_208), k2_tarski(A_208, B_209))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_2980])).
% 9.12/3.65  tff(c_38, plain, (![A_32, B_33]: (k5_xboole_0(A_32, k4_xboole_0(B_33, A_32))=k2_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.12/3.65  tff(c_3072, plain, (![A_208, B_209]: (k2_xboole_0(k2_tarski(A_208, B_209), k1_tarski(A_208))=k5_xboole_0(k2_tarski(A_208, B_209), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3037, c_38])).
% 9.12/3.65  tff(c_18516, plain, (![A_402, B_403]: (k2_xboole_0(k2_tarski(A_402, B_403), k1_tarski(A_402))=k2_tarski(A_402, B_403))), inference(demodulation, [status(thm), theory('equality')], [c_525, c_4, c_3072])).
% 9.12/3.65  tff(c_2754, plain, (![B_33, A_32]: (k5_xboole_0(k4_xboole_0(B_33, A_32), A_32)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_32, B_33)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_2646])).
% 9.12/3.65  tff(c_2788, plain, (![B_33, A_32]: (k5_xboole_0(k4_xboole_0(B_33, A_32), A_32)=k2_xboole_0(A_32, B_33))), inference(demodulation, [status(thm), theory('equality')], [c_525, c_2754])).
% 9.12/3.65  tff(c_501, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_472])).
% 9.12/3.65  tff(c_2736, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k5_xboole_0(k1_xboole_0, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_501, c_2646])).
% 9.12/3.65  tff(c_2784, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k4_xboole_0(B_2, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_525, c_2736])).
% 9.12/3.65  tff(c_6122, plain, (![A_262, B_263, C_264]: (k5_xboole_0(A_262, k5_xboole_0(k3_xboole_0(A_262, B_263), C_264))=k5_xboole_0(k4_xboole_0(A_262, B_263), C_264))), inference(superposition, [status(thm), theory('equality')], [c_20, c_617])).
% 9.12/3.65  tff(c_6232, plain, (![A_1, B_2]: (k5_xboole_0(k4_xboole_0(A_1, B_2), B_2)=k5_xboole_0(A_1, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2784, c_6122])).
% 9.12/3.65  tff(c_6345, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_2788, c_38, c_6232])).
% 9.12/3.65  tff(c_18546, plain, (![A_402, B_403]: (k2_xboole_0(k1_tarski(A_402), k2_tarski(A_402, B_403))=k2_tarski(A_402, B_403))), inference(superposition, [status(thm), theory('equality')], [c_18516, c_6345])).
% 9.12/3.65  tff(c_56, plain, (k2_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_3', '#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.12/3.65  tff(c_18692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18546, c_56])).
% 9.12/3.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.12/3.65  
% 9.12/3.65  Inference rules
% 9.12/3.65  ----------------------
% 9.12/3.65  #Ref     : 0
% 9.12/3.65  #Sup     : 4644
% 9.12/3.65  #Fact    : 0
% 9.12/3.65  #Define  : 0
% 9.12/3.65  #Split   : 0
% 9.12/3.65  #Chain   : 0
% 9.12/3.65  #Close   : 0
% 9.12/3.65  
% 9.12/3.65  Ordering : KBO
% 9.12/3.65  
% 9.12/3.65  Simplification rules
% 9.12/3.65  ----------------------
% 9.12/3.65  #Subsume      : 327
% 9.12/3.65  #Demod        : 5639
% 9.12/3.65  #Tautology    : 2878
% 9.12/3.65  #SimpNegUnit  : 16
% 9.12/3.65  #BackRed      : 4
% 9.12/3.65  
% 9.12/3.65  #Partial instantiations: 0
% 9.12/3.65  #Strategies tried      : 1
% 9.12/3.65  
% 9.12/3.65  Timing (in seconds)
% 9.12/3.65  ----------------------
% 9.12/3.65  Preprocessing        : 0.33
% 9.12/3.65  Parsing              : 0.18
% 9.12/3.65  CNF conversion       : 0.02
% 9.12/3.65  Main loop            : 2.54
% 9.12/3.65  Inferencing          : 0.53
% 9.12/3.65  Reduction            : 1.51
% 9.12/3.65  Demodulation         : 1.36
% 9.12/3.65  BG Simplification    : 0.07
% 9.12/3.65  Subsumption          : 0.32
% 9.12/3.65  Abstraction          : 0.11
% 9.12/3.65  MUC search           : 0.00
% 9.12/3.65  Cooper               : 0.00
% 9.12/3.65  Total                : 2.91
% 9.12/3.65  Index Insertion      : 0.00
% 9.12/3.65  Index Deletion       : 0.00
% 9.12/3.65  Index Matching       : 0.00
% 9.12/3.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
