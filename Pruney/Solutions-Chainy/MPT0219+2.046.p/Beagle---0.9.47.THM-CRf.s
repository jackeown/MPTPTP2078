%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:55 EST 2020

% Result     : Theorem 10.80s
% Output     : CNFRefutation 10.80s
% Verified   : 
% Statistics : Number of formulae       :  121 (1259 expanded)
%              Number of leaves         :   32 ( 438 expanded)
%              Depth                    :   22
%              Number of atoms          :  132 (1829 expanded)
%              Number of equality atoms :   83 ( 919 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_54,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_56,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_3')) = k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_139,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_169,plain,(
    ! [A_52] : k3_xboole_0(k1_xboole_0,A_52) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_139])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_178,plain,(
    ! [A_52] : k3_xboole_0(A_52,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_2])).

tff(c_294,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k3_xboole_0(A_62,B_63)) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_306,plain,(
    ! [A_52] : k5_xboole_0(A_52,k1_xboole_0) = k4_xboole_0(A_52,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_294])).

tff(c_645,plain,(
    ! [A_91,B_92,C_93] : k5_xboole_0(k5_xboole_0(A_91,B_92),C_93) = k5_xboole_0(A_91,k5_xboole_0(B_92,C_93)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_663,plain,(
    ! [A_91,B_92] : k5_xboole_0(A_91,k5_xboole_0(B_92,k1_xboole_0)) = k4_xboole_0(k5_xboole_0(A_91,B_92),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_306])).

tff(c_1241,plain,(
    ! [A_114,B_115] : k5_xboole_0(A_114,k4_xboole_0(B_115,k1_xboole_0)) = k4_xboole_0(k5_xboole_0(A_114,B_115),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_663])).

tff(c_32,plain,(
    ! [A_17] : k2_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_151,plain,(
    ! [A_20] : k3_xboole_0(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_139])).

tff(c_321,plain,(
    ! [A_64] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_294])).

tff(c_309,plain,(
    ! [A_20] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_294])).

tff(c_324,plain,(
    ! [A_64,A_20] : k4_xboole_0(k1_xboole_0,A_64) = k4_xboole_0(k1_xboole_0,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_309])).

tff(c_396,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k4_xboole_0(B_72,A_71)) = k2_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_408,plain,(
    ! [A_64,A_20] : k5_xboole_0(A_64,k4_xboole_0(k1_xboole_0,A_20)) = k2_xboole_0(A_64,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_396])).

tff(c_415,plain,(
    ! [A_64,A_20] : k5_xboole_0(A_64,k4_xboole_0(k1_xboole_0,A_20)) = A_64 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_408])).

tff(c_1277,plain,(
    ! [A_114] : k4_xboole_0(k5_xboole_0(A_114,k1_xboole_0),k1_xboole_0) = A_114 ),
    inference(superposition,[status(thm),theory(equality)],[c_1241,c_415])).

tff(c_1336,plain,(
    ! [A_114] : k4_xboole_0(k4_xboole_0(A_114,k1_xboole_0),k1_xboole_0) = A_114 ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_1277])).

tff(c_28,plain,(
    ! [B_14] : r1_tarski(B_14,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_150,plain,(
    ! [B_14] : k3_xboole_0(B_14,B_14) = B_14 ),
    inference(resolution,[status(thm)],[c_28,c_139])).

tff(c_312,plain,(
    ! [B_14] : k5_xboole_0(B_14,B_14) = k4_xboole_0(B_14,B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_294])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1010,plain,(
    ! [A_104,B_105,C_106] :
      ( r2_hidden(A_104,B_105)
      | r2_hidden(A_104,C_106)
      | ~ r2_hidden(A_104,k5_xboole_0(B_105,C_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1052,plain,(
    ! [B_105,C_106,B_4] :
      ( r2_hidden('#skF_1'(k5_xboole_0(B_105,C_106),B_4),B_105)
      | r2_hidden('#skF_1'(k5_xboole_0(B_105,C_106),B_4),C_106)
      | r1_tarski(k5_xboole_0(B_105,C_106),B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_1010])).

tff(c_13088,plain,(
    ! [C_106,B_4] :
      ( r1_tarski(k5_xboole_0(C_106,C_106),B_4)
      | r2_hidden('#skF_1'(k5_xboole_0(C_106,C_106),B_4),C_106) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1052])).

tff(c_14609,plain,(
    ! [C_349,B_350] :
      ( r1_tarski(k4_xboole_0(C_349,C_349),B_350)
      | r2_hidden('#skF_1'(k4_xboole_0(C_349,C_349),B_350),C_349) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_312,c_13088])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14727,plain,(
    ! [C_351] : r1_tarski(k4_xboole_0(C_351,C_351),C_351) ),
    inference(resolution,[status(thm)],[c_14609,c_6])).

tff(c_370,plain,(
    ! [B_68,A_69] :
      ( B_68 = A_69
      | ~ r1_tarski(B_68,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_382,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36,c_370])).

tff(c_14752,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14727,c_382])).

tff(c_730,plain,(
    ! [A_91,B_92] : k5_xboole_0(A_91,k4_xboole_0(B_92,k1_xboole_0)) = k4_xboole_0(k5_xboole_0(A_91,B_92),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_663])).

tff(c_14912,plain,(
    ! [A_91] : k4_xboole_0(k5_xboole_0(A_91,k1_xboole_0),k1_xboole_0) = k5_xboole_0(A_91,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14752,c_730])).

tff(c_14978,plain,(
    ! [A_91] : k4_xboole_0(A_91,k1_xboole_0) = A_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1336,c_306,c_306,c_14912])).

tff(c_14995,plain,(
    ! [A_52] : k5_xboole_0(A_52,k1_xboole_0) = A_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14978,c_306])).

tff(c_13098,plain,(
    ! [C_106,B_4] :
      ( r1_tarski(k4_xboole_0(C_106,C_106),B_4)
      | r2_hidden('#skF_1'(k4_xboole_0(C_106,C_106),B_4),C_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_312,c_13088])).

tff(c_1397,plain,(
    ! [A_117,C_118,B_119] :
      ( ~ r2_hidden(A_117,C_118)
      | ~ r2_hidden(A_117,B_119)
      | ~ r2_hidden(A_117,k5_xboole_0(B_119,C_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3690,plain,(
    ! [A_159,B_160] :
      ( ~ r2_hidden(A_159,B_160)
      | ~ r2_hidden(A_159,B_160)
      | ~ r2_hidden(A_159,k4_xboole_0(B_160,B_160)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_1397])).

tff(c_20010,plain,(
    ! [B_416,B_417] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(B_416,B_416),B_417),B_416)
      | r1_tarski(k4_xboole_0(B_416,B_416),B_417) ) ),
    inference(resolution,[status(thm)],[c_8,c_3690])).

tff(c_20116,plain,(
    ! [C_418,B_419] : r1_tarski(k4_xboole_0(C_418,C_418),B_419) ),
    inference(resolution,[status(thm)],[c_13098,c_20010])).

tff(c_20141,plain,(
    ! [C_418] : k4_xboole_0(C_418,C_418) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20116,c_382])).

tff(c_20323,plain,(
    ! [B_422] : k5_xboole_0(B_422,B_422) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20141,c_312])).

tff(c_315,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_294])).

tff(c_684,plain,(
    ! [A_1,B_2,C_93] : k5_xboole_0(A_1,k5_xboole_0(k3_xboole_0(B_2,A_1),C_93)) = k5_xboole_0(k4_xboole_0(A_1,B_2),C_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_645])).

tff(c_20357,plain,(
    ! [A_1,B_2] : k5_xboole_0(k4_xboole_0(A_1,B_2),k3_xboole_0(B_2,A_1)) = k5_xboole_0(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20323,c_684])).

tff(c_22503,plain,(
    ! [A_444,B_445] : k5_xboole_0(k4_xboole_0(A_444,B_445),k3_xboole_0(B_445,A_444)) = A_444 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14995,c_20357])).

tff(c_42,plain,(
    ! [A_26,B_27] : k5_xboole_0(A_26,k4_xboole_0(B_27,A_26)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8535,plain,(
    ! [A_247,B_248,B_249] : k5_xboole_0(A_247,k5_xboole_0(B_248,k4_xboole_0(B_249,k5_xboole_0(A_247,B_248)))) = k2_xboole_0(k5_xboole_0(A_247,B_248),B_249) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_645])).

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_712,plain,(
    ! [B_14,C_93] : k5_xboole_0(k4_xboole_0(B_14,B_14),C_93) = k5_xboole_0(B_14,k5_xboole_0(B_14,C_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_645])).

tff(c_2718,plain,(
    ! [A_145,B_146,C_147] : k5_xboole_0(A_145,k5_xboole_0(k4_xboole_0(B_146,A_145),C_147)) = k5_xboole_0(k2_xboole_0(A_145,B_146),C_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_645])).

tff(c_2839,plain,(
    ! [B_14,C_93] : k5_xboole_0(B_14,k5_xboole_0(B_14,k5_xboole_0(B_14,C_93))) = k5_xboole_0(k2_xboole_0(B_14,B_14),C_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_712,c_2718])).

tff(c_2987,plain,(
    ! [B_149,C_150] : k5_xboole_0(B_149,k5_xboole_0(B_149,k5_xboole_0(B_149,C_150))) = k5_xboole_0(B_149,C_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2839])).

tff(c_3167,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k5_xboole_0(A_15,k4_xboole_0(A_15,B_16))) = k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2987])).

tff(c_3216,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k5_xboole_0(A_15,k4_xboole_0(A_15,B_16))) = k4_xboole_0(A_15,B_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3167])).

tff(c_8576,plain,(
    ! [B_249] : k4_xboole_0(B_249,k5_xboole_0(B_249,B_249)) = k2_xboole_0(k5_xboole_0(B_249,B_249),B_249) ),
    inference(superposition,[status(thm),theory(equality)],[c_8535,c_3216])).

tff(c_8856,plain,(
    ! [B_249] : k4_xboole_0(B_249,k4_xboole_0(B_249,B_249)) = k2_xboole_0(k4_xboole_0(B_249,B_249),B_249) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_312,c_8576])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16181,plain,(
    ! [C_358] : k3_xboole_0(k4_xboole_0(C_358,C_358),C_358) = k4_xboole_0(C_358,C_358) ),
    inference(resolution,[status(thm)],[c_14727,c_34])).

tff(c_16463,plain,(
    ! [A_361] : k3_xboole_0(A_361,k4_xboole_0(A_361,A_361)) = k4_xboole_0(A_361,A_361) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_16181])).

tff(c_16482,plain,(
    ! [A_361] : k5_xboole_0(A_361,k4_xboole_0(A_361,A_361)) = k4_xboole_0(A_361,k4_xboole_0(A_361,A_361)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16463,c_30])).

tff(c_16510,plain,(
    ! [A_361] : k2_xboole_0(k4_xboole_0(A_361,A_361),A_361) = A_361 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8856,c_10,c_42,c_16482])).

tff(c_20157,plain,(
    ! [A_361] : k2_xboole_0(k1_xboole_0,A_361) = A_361 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20141,c_16510])).

tff(c_20166,plain,(
    ! [B_14] : k5_xboole_0(B_14,B_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20141,c_312])).

tff(c_709,plain,(
    ! [A_91,B_92,B_27] : k5_xboole_0(A_91,k5_xboole_0(B_92,k4_xboole_0(B_27,k5_xboole_0(A_91,B_92)))) = k2_xboole_0(k5_xboole_0(A_91,B_92),B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_645])).

tff(c_20406,plain,(
    ! [B_422,B_27] : k5_xboole_0(B_422,k5_xboole_0(B_422,k4_xboole_0(B_27,k1_xboole_0))) = k2_xboole_0(k5_xboole_0(B_422,B_422),B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_20323,c_709])).

tff(c_20472,plain,(
    ! [B_422,B_27] : k5_xboole_0(B_422,k5_xboole_0(B_422,B_27)) = B_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20157,c_20166,c_14978,c_20406])).

tff(c_24217,plain,(
    ! [A_464,B_465] : k5_xboole_0(k4_xboole_0(A_464,B_465),A_464) = k3_xboole_0(B_465,A_464) ),
    inference(superposition,[status(thm),theory(equality)],[c_22503,c_20472])).

tff(c_705,plain,(
    ! [A_26,B_27,C_93] : k5_xboole_0(A_26,k5_xboole_0(k4_xboole_0(B_27,A_26),C_93)) = k5_xboole_0(k2_xboole_0(A_26,B_27),C_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_645])).

tff(c_24332,plain,(
    ! [B_465,A_464] : k5_xboole_0(k2_xboole_0(B_465,A_464),A_464) = k5_xboole_0(B_465,k3_xboole_0(B_465,A_464)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24217,c_705])).

tff(c_24965,plain,(
    ! [B_475,A_476] : k5_xboole_0(k2_xboole_0(B_475,A_476),A_476) = k4_xboole_0(B_475,A_476) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24332])).

tff(c_25115,plain,(
    k5_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_24965])).

tff(c_7910,plain,(
    ! [A_242,B_243,B_244] : k5_xboole_0(A_242,k5_xboole_0(B_243,k3_xboole_0(k5_xboole_0(A_242,B_243),B_244))) = k4_xboole_0(k5_xboole_0(A_242,B_243),B_244) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_645])).

tff(c_8193,plain,(
    ! [A_242,B_243] : k5_xboole_0(A_242,k5_xboole_0(B_243,k5_xboole_0(A_242,B_243))) = k4_xboole_0(k5_xboole_0(A_242,B_243),k5_xboole_0(A_242,B_243)) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_7910])).

tff(c_21120,plain,(
    ! [A_432,B_433] : k5_xboole_0(A_432,k5_xboole_0(B_433,k5_xboole_0(A_432,B_433))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20141,c_8193])).

tff(c_21128,plain,(
    ! [B_433,A_432] : k5_xboole_0(B_433,k5_xboole_0(A_432,B_433)) = k5_xboole_0(A_432,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_21120,c_20472])).

tff(c_21351,plain,(
    ! [B_433,A_432] : k5_xboole_0(B_433,k5_xboole_0(A_432,B_433)) = A_432 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14995,c_21128])).

tff(c_25453,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_3'))) = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_25115,c_21351])).

tff(c_26091,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_25453,c_42])).

tff(c_38,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26152,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26091,c_38])).

tff(c_52,plain,(
    ! [B_39,A_38] :
      ( B_39 = A_38
      | ~ r1_tarski(k1_tarski(A_38),k1_tarski(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26171,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26152,c_52])).

tff(c_26180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_26171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:25:53 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.80/4.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.80/4.48  
% 10.80/4.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.80/4.48  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.80/4.48  
% 10.80/4.48  %Foreground sorts:
% 10.80/4.48  
% 10.80/4.48  
% 10.80/4.48  %Background operators:
% 10.80/4.48  
% 10.80/4.48  
% 10.80/4.48  %Foreground operators:
% 10.80/4.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.80/4.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.80/4.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.80/4.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.80/4.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.80/4.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.80/4.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.80/4.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.80/4.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.80/4.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.80/4.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.80/4.48  tff('#skF_2', type, '#skF_2': $i).
% 10.80/4.48  tff('#skF_3', type, '#skF_3': $i).
% 10.80/4.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.80/4.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.80/4.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.80/4.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.80/4.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.80/4.48  
% 10.80/4.51  tff(f_82, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 10.80/4.51  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.80/4.51  tff(f_59, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.80/4.51  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.80/4.51  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.80/4.51  tff(f_63, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.80/4.51  tff(f_53, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 10.80/4.51  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.80/4.51  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.80/4.51  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.80/4.51  tff(f_43, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 10.80/4.51  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 10.80/4.51  tff(f_61, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 10.80/4.51  tff(f_77, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 10.80/4.51  tff(c_54, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.80/4.51  tff(c_56, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3'))=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.80/4.51  tff(c_30, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.80/4.51  tff(c_36, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.80/4.51  tff(c_139, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=A_49 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.80/4.51  tff(c_169, plain, (![A_52]: (k3_xboole_0(k1_xboole_0, A_52)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_139])).
% 10.80/4.51  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.80/4.51  tff(c_178, plain, (![A_52]: (k3_xboole_0(A_52, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_169, c_2])).
% 10.80/4.51  tff(c_294, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k3_xboole_0(A_62, B_63))=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.80/4.51  tff(c_306, plain, (![A_52]: (k5_xboole_0(A_52, k1_xboole_0)=k4_xboole_0(A_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_178, c_294])).
% 10.80/4.51  tff(c_645, plain, (![A_91, B_92, C_93]: (k5_xboole_0(k5_xboole_0(A_91, B_92), C_93)=k5_xboole_0(A_91, k5_xboole_0(B_92, C_93)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.80/4.51  tff(c_663, plain, (![A_91, B_92]: (k5_xboole_0(A_91, k5_xboole_0(B_92, k1_xboole_0))=k4_xboole_0(k5_xboole_0(A_91, B_92), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_645, c_306])).
% 10.80/4.51  tff(c_1241, plain, (![A_114, B_115]: (k5_xboole_0(A_114, k4_xboole_0(B_115, k1_xboole_0))=k4_xboole_0(k5_xboole_0(A_114, B_115), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_663])).
% 10.80/4.51  tff(c_32, plain, (![A_17]: (k2_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.80/4.51  tff(c_151, plain, (![A_20]: (k3_xboole_0(k1_xboole_0, A_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_139])).
% 10.80/4.51  tff(c_321, plain, (![A_64]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_64))), inference(superposition, [status(thm), theory('equality')], [c_151, c_294])).
% 10.80/4.51  tff(c_309, plain, (![A_20]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_20))), inference(superposition, [status(thm), theory('equality')], [c_151, c_294])).
% 10.80/4.51  tff(c_324, plain, (![A_64, A_20]: (k4_xboole_0(k1_xboole_0, A_64)=k4_xboole_0(k1_xboole_0, A_20))), inference(superposition, [status(thm), theory('equality')], [c_321, c_309])).
% 10.80/4.51  tff(c_396, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k4_xboole_0(B_72, A_71))=k2_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.80/4.51  tff(c_408, plain, (![A_64, A_20]: (k5_xboole_0(A_64, k4_xboole_0(k1_xboole_0, A_20))=k2_xboole_0(A_64, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_324, c_396])).
% 10.80/4.51  tff(c_415, plain, (![A_64, A_20]: (k5_xboole_0(A_64, k4_xboole_0(k1_xboole_0, A_20))=A_64)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_408])).
% 10.80/4.51  tff(c_1277, plain, (![A_114]: (k4_xboole_0(k5_xboole_0(A_114, k1_xboole_0), k1_xboole_0)=A_114)), inference(superposition, [status(thm), theory('equality')], [c_1241, c_415])).
% 10.80/4.51  tff(c_1336, plain, (![A_114]: (k4_xboole_0(k4_xboole_0(A_114, k1_xboole_0), k1_xboole_0)=A_114)), inference(demodulation, [status(thm), theory('equality')], [c_306, c_1277])).
% 10.80/4.51  tff(c_28, plain, (![B_14]: (r1_tarski(B_14, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.80/4.51  tff(c_150, plain, (![B_14]: (k3_xboole_0(B_14, B_14)=B_14)), inference(resolution, [status(thm)], [c_28, c_139])).
% 10.80/4.51  tff(c_312, plain, (![B_14]: (k5_xboole_0(B_14, B_14)=k4_xboole_0(B_14, B_14))), inference(superposition, [status(thm), theory('equality')], [c_150, c_294])).
% 10.80/4.51  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.80/4.51  tff(c_1010, plain, (![A_104, B_105, C_106]: (r2_hidden(A_104, B_105) | r2_hidden(A_104, C_106) | ~r2_hidden(A_104, k5_xboole_0(B_105, C_106)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.80/4.51  tff(c_1052, plain, (![B_105, C_106, B_4]: (r2_hidden('#skF_1'(k5_xboole_0(B_105, C_106), B_4), B_105) | r2_hidden('#skF_1'(k5_xboole_0(B_105, C_106), B_4), C_106) | r1_tarski(k5_xboole_0(B_105, C_106), B_4))), inference(resolution, [status(thm)], [c_8, c_1010])).
% 10.80/4.51  tff(c_13088, plain, (![C_106, B_4]: (r1_tarski(k5_xboole_0(C_106, C_106), B_4) | r2_hidden('#skF_1'(k5_xboole_0(C_106, C_106), B_4), C_106))), inference(factorization, [status(thm), theory('equality')], [c_1052])).
% 10.80/4.51  tff(c_14609, plain, (![C_349, B_350]: (r1_tarski(k4_xboole_0(C_349, C_349), B_350) | r2_hidden('#skF_1'(k4_xboole_0(C_349, C_349), B_350), C_349))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_312, c_13088])).
% 10.80/4.51  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.80/4.51  tff(c_14727, plain, (![C_351]: (r1_tarski(k4_xboole_0(C_351, C_351), C_351))), inference(resolution, [status(thm)], [c_14609, c_6])).
% 10.80/4.51  tff(c_370, plain, (![B_68, A_69]: (B_68=A_69 | ~r1_tarski(B_68, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.80/4.51  tff(c_382, plain, (![A_20]: (k1_xboole_0=A_20 | ~r1_tarski(A_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_370])).
% 10.80/4.51  tff(c_14752, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_14727, c_382])).
% 10.80/4.51  tff(c_730, plain, (![A_91, B_92]: (k5_xboole_0(A_91, k4_xboole_0(B_92, k1_xboole_0))=k4_xboole_0(k5_xboole_0(A_91, B_92), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_663])).
% 10.80/4.51  tff(c_14912, plain, (![A_91]: (k4_xboole_0(k5_xboole_0(A_91, k1_xboole_0), k1_xboole_0)=k5_xboole_0(A_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14752, c_730])).
% 10.80/4.51  tff(c_14978, plain, (![A_91]: (k4_xboole_0(A_91, k1_xboole_0)=A_91)), inference(demodulation, [status(thm), theory('equality')], [c_1336, c_306, c_306, c_14912])).
% 10.80/4.51  tff(c_14995, plain, (![A_52]: (k5_xboole_0(A_52, k1_xboole_0)=A_52)), inference(demodulation, [status(thm), theory('equality')], [c_14978, c_306])).
% 10.80/4.51  tff(c_13098, plain, (![C_106, B_4]: (r1_tarski(k4_xboole_0(C_106, C_106), B_4) | r2_hidden('#skF_1'(k4_xboole_0(C_106, C_106), B_4), C_106))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_312, c_13088])).
% 10.80/4.51  tff(c_1397, plain, (![A_117, C_118, B_119]: (~r2_hidden(A_117, C_118) | ~r2_hidden(A_117, B_119) | ~r2_hidden(A_117, k5_xboole_0(B_119, C_118)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.80/4.51  tff(c_3690, plain, (![A_159, B_160]: (~r2_hidden(A_159, B_160) | ~r2_hidden(A_159, B_160) | ~r2_hidden(A_159, k4_xboole_0(B_160, B_160)))), inference(superposition, [status(thm), theory('equality')], [c_312, c_1397])).
% 10.80/4.51  tff(c_20010, plain, (![B_416, B_417]: (~r2_hidden('#skF_1'(k4_xboole_0(B_416, B_416), B_417), B_416) | r1_tarski(k4_xboole_0(B_416, B_416), B_417))), inference(resolution, [status(thm)], [c_8, c_3690])).
% 10.80/4.51  tff(c_20116, plain, (![C_418, B_419]: (r1_tarski(k4_xboole_0(C_418, C_418), B_419))), inference(resolution, [status(thm)], [c_13098, c_20010])).
% 10.80/4.51  tff(c_20141, plain, (![C_418]: (k4_xboole_0(C_418, C_418)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20116, c_382])).
% 10.80/4.51  tff(c_20323, plain, (![B_422]: (k5_xboole_0(B_422, B_422)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20141, c_312])).
% 10.80/4.51  tff(c_315, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_294])).
% 10.80/4.51  tff(c_684, plain, (![A_1, B_2, C_93]: (k5_xboole_0(A_1, k5_xboole_0(k3_xboole_0(B_2, A_1), C_93))=k5_xboole_0(k4_xboole_0(A_1, B_2), C_93))), inference(superposition, [status(thm), theory('equality')], [c_315, c_645])).
% 10.80/4.51  tff(c_20357, plain, (![A_1, B_2]: (k5_xboole_0(k4_xboole_0(A_1, B_2), k3_xboole_0(B_2, A_1))=k5_xboole_0(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20323, c_684])).
% 10.80/4.51  tff(c_22503, plain, (![A_444, B_445]: (k5_xboole_0(k4_xboole_0(A_444, B_445), k3_xboole_0(B_445, A_444))=A_444)), inference(demodulation, [status(thm), theory('equality')], [c_14995, c_20357])).
% 10.80/4.51  tff(c_42, plain, (![A_26, B_27]: (k5_xboole_0(A_26, k4_xboole_0(B_27, A_26))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.80/4.51  tff(c_8535, plain, (![A_247, B_248, B_249]: (k5_xboole_0(A_247, k5_xboole_0(B_248, k4_xboole_0(B_249, k5_xboole_0(A_247, B_248))))=k2_xboole_0(k5_xboole_0(A_247, B_248), B_249))), inference(superposition, [status(thm), theory('equality')], [c_42, c_645])).
% 10.80/4.51  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.80/4.51  tff(c_712, plain, (![B_14, C_93]: (k5_xboole_0(k4_xboole_0(B_14, B_14), C_93)=k5_xboole_0(B_14, k5_xboole_0(B_14, C_93)))), inference(superposition, [status(thm), theory('equality')], [c_312, c_645])).
% 10.80/4.51  tff(c_2718, plain, (![A_145, B_146, C_147]: (k5_xboole_0(A_145, k5_xboole_0(k4_xboole_0(B_146, A_145), C_147))=k5_xboole_0(k2_xboole_0(A_145, B_146), C_147))), inference(superposition, [status(thm), theory('equality')], [c_42, c_645])).
% 10.80/4.51  tff(c_2839, plain, (![B_14, C_93]: (k5_xboole_0(B_14, k5_xboole_0(B_14, k5_xboole_0(B_14, C_93)))=k5_xboole_0(k2_xboole_0(B_14, B_14), C_93))), inference(superposition, [status(thm), theory('equality')], [c_712, c_2718])).
% 10.80/4.51  tff(c_2987, plain, (![B_149, C_150]: (k5_xboole_0(B_149, k5_xboole_0(B_149, k5_xboole_0(B_149, C_150)))=k5_xboole_0(B_149, C_150))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2839])).
% 10.80/4.51  tff(c_3167, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k5_xboole_0(A_15, k4_xboole_0(A_15, B_16)))=k5_xboole_0(A_15, k3_xboole_0(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2987])).
% 10.80/4.51  tff(c_3216, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k5_xboole_0(A_15, k4_xboole_0(A_15, B_16)))=k4_xboole_0(A_15, B_16))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3167])).
% 10.80/4.51  tff(c_8576, plain, (![B_249]: (k4_xboole_0(B_249, k5_xboole_0(B_249, B_249))=k2_xboole_0(k5_xboole_0(B_249, B_249), B_249))), inference(superposition, [status(thm), theory('equality')], [c_8535, c_3216])).
% 10.80/4.51  tff(c_8856, plain, (![B_249]: (k4_xboole_0(B_249, k4_xboole_0(B_249, B_249))=k2_xboole_0(k4_xboole_0(B_249, B_249), B_249))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_312, c_8576])).
% 10.80/4.51  tff(c_34, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.80/4.51  tff(c_16181, plain, (![C_358]: (k3_xboole_0(k4_xboole_0(C_358, C_358), C_358)=k4_xboole_0(C_358, C_358))), inference(resolution, [status(thm)], [c_14727, c_34])).
% 10.80/4.51  tff(c_16463, plain, (![A_361]: (k3_xboole_0(A_361, k4_xboole_0(A_361, A_361))=k4_xboole_0(A_361, A_361))), inference(superposition, [status(thm), theory('equality')], [c_2, c_16181])).
% 10.80/4.51  tff(c_16482, plain, (![A_361]: (k5_xboole_0(A_361, k4_xboole_0(A_361, A_361))=k4_xboole_0(A_361, k4_xboole_0(A_361, A_361)))), inference(superposition, [status(thm), theory('equality')], [c_16463, c_30])).
% 10.80/4.51  tff(c_16510, plain, (![A_361]: (k2_xboole_0(k4_xboole_0(A_361, A_361), A_361)=A_361)), inference(demodulation, [status(thm), theory('equality')], [c_8856, c_10, c_42, c_16482])).
% 10.80/4.51  tff(c_20157, plain, (![A_361]: (k2_xboole_0(k1_xboole_0, A_361)=A_361)), inference(demodulation, [status(thm), theory('equality')], [c_20141, c_16510])).
% 10.80/4.51  tff(c_20166, plain, (![B_14]: (k5_xboole_0(B_14, B_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20141, c_312])).
% 10.80/4.51  tff(c_709, plain, (![A_91, B_92, B_27]: (k5_xboole_0(A_91, k5_xboole_0(B_92, k4_xboole_0(B_27, k5_xboole_0(A_91, B_92))))=k2_xboole_0(k5_xboole_0(A_91, B_92), B_27))), inference(superposition, [status(thm), theory('equality')], [c_42, c_645])).
% 10.80/4.51  tff(c_20406, plain, (![B_422, B_27]: (k5_xboole_0(B_422, k5_xboole_0(B_422, k4_xboole_0(B_27, k1_xboole_0)))=k2_xboole_0(k5_xboole_0(B_422, B_422), B_27))), inference(superposition, [status(thm), theory('equality')], [c_20323, c_709])).
% 10.80/4.51  tff(c_20472, plain, (![B_422, B_27]: (k5_xboole_0(B_422, k5_xboole_0(B_422, B_27))=B_27)), inference(demodulation, [status(thm), theory('equality')], [c_20157, c_20166, c_14978, c_20406])).
% 10.80/4.51  tff(c_24217, plain, (![A_464, B_465]: (k5_xboole_0(k4_xboole_0(A_464, B_465), A_464)=k3_xboole_0(B_465, A_464))), inference(superposition, [status(thm), theory('equality')], [c_22503, c_20472])).
% 10.80/4.51  tff(c_705, plain, (![A_26, B_27, C_93]: (k5_xboole_0(A_26, k5_xboole_0(k4_xboole_0(B_27, A_26), C_93))=k5_xboole_0(k2_xboole_0(A_26, B_27), C_93))), inference(superposition, [status(thm), theory('equality')], [c_42, c_645])).
% 10.80/4.51  tff(c_24332, plain, (![B_465, A_464]: (k5_xboole_0(k2_xboole_0(B_465, A_464), A_464)=k5_xboole_0(B_465, k3_xboole_0(B_465, A_464)))), inference(superposition, [status(thm), theory('equality')], [c_24217, c_705])).
% 10.80/4.51  tff(c_24965, plain, (![B_475, A_476]: (k5_xboole_0(k2_xboole_0(B_475, A_476), A_476)=k4_xboole_0(B_475, A_476))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24332])).
% 10.80/4.51  tff(c_25115, plain, (k5_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_24965])).
% 10.80/4.51  tff(c_7910, plain, (![A_242, B_243, B_244]: (k5_xboole_0(A_242, k5_xboole_0(B_243, k3_xboole_0(k5_xboole_0(A_242, B_243), B_244)))=k4_xboole_0(k5_xboole_0(A_242, B_243), B_244))), inference(superposition, [status(thm), theory('equality')], [c_30, c_645])).
% 10.80/4.51  tff(c_8193, plain, (![A_242, B_243]: (k5_xboole_0(A_242, k5_xboole_0(B_243, k5_xboole_0(A_242, B_243)))=k4_xboole_0(k5_xboole_0(A_242, B_243), k5_xboole_0(A_242, B_243)))), inference(superposition, [status(thm), theory('equality')], [c_150, c_7910])).
% 10.80/4.51  tff(c_21120, plain, (![A_432, B_433]: (k5_xboole_0(A_432, k5_xboole_0(B_433, k5_xboole_0(A_432, B_433)))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20141, c_8193])).
% 10.80/4.51  tff(c_21128, plain, (![B_433, A_432]: (k5_xboole_0(B_433, k5_xboole_0(A_432, B_433))=k5_xboole_0(A_432, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_21120, c_20472])).
% 10.80/4.51  tff(c_21351, plain, (![B_433, A_432]: (k5_xboole_0(B_433, k5_xboole_0(A_432, B_433))=A_432)), inference(demodulation, [status(thm), theory('equality')], [c_14995, c_21128])).
% 10.80/4.51  tff(c_25453, plain, (k5_xboole_0(k1_tarski('#skF_3'), k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3')))=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_25115, c_21351])).
% 10.80/4.51  tff(c_26091, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_25453, c_42])).
% 10.80/4.51  tff(c_38, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.80/4.51  tff(c_26152, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_26091, c_38])).
% 10.80/4.51  tff(c_52, plain, (![B_39, A_38]: (B_39=A_38 | ~r1_tarski(k1_tarski(A_38), k1_tarski(B_39)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.80/4.51  tff(c_26171, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_26152, c_52])).
% 10.80/4.51  tff(c_26180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_26171])).
% 10.80/4.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.80/4.51  
% 10.80/4.51  Inference rules
% 10.80/4.51  ----------------------
% 10.80/4.51  #Ref     : 0
% 10.80/4.51  #Sup     : 6715
% 10.80/4.51  #Fact    : 4
% 10.80/4.51  #Define  : 0
% 10.80/4.51  #Split   : 0
% 10.80/4.51  #Chain   : 0
% 10.80/4.51  #Close   : 0
% 10.80/4.51  
% 10.80/4.51  Ordering : KBO
% 10.80/4.51  
% 10.80/4.51  Simplification rules
% 10.80/4.51  ----------------------
% 10.80/4.51  #Subsume      : 1010
% 10.80/4.51  #Demod        : 8113
% 10.80/4.51  #Tautology    : 2730
% 10.80/4.51  #SimpNegUnit  : 1
% 10.80/4.51  #BackRed      : 63
% 10.80/4.51  
% 10.80/4.51  #Partial instantiations: 0
% 10.80/4.51  #Strategies tried      : 1
% 10.80/4.51  
% 10.80/4.51  Timing (in seconds)
% 10.80/4.51  ----------------------
% 11.02/4.51  Preprocessing        : 0.33
% 11.02/4.51  Parsing              : 0.18
% 11.02/4.51  CNF conversion       : 0.02
% 11.02/4.51  Main loop            : 3.34
% 11.02/4.51  Inferencing          : 0.70
% 11.02/4.51  Reduction            : 1.75
% 11.02/4.51  Demodulation         : 1.54
% 11.02/4.51  BG Simplification    : 0.10
% 11.02/4.51  Subsumption          : 0.60
% 11.02/4.51  Abstraction          : 0.14
% 11.02/4.51  MUC search           : 0.00
% 11.02/4.51  Cooper               : 0.00
% 11.02/4.51  Total                : 3.72
% 11.02/4.51  Index Insertion      : 0.00
% 11.02/4.51  Index Deletion       : 0.00
% 11.02/4.51  Index Matching       : 0.00
% 11.02/4.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
