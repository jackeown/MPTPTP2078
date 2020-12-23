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
% DateTime   : Thu Dec  3 09:54:36 EST 2020

% Result     : Theorem 12.90s
% Output     : CNFRefutation 12.90s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 823 expanded)
%              Number of leaves         :   33 ( 291 expanded)
%              Depth                    :   22
%              Number of atoms          :  110 ( 988 expanded)
%              Number of equality atoms :   86 ( 617 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_67,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_44,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1193,plain,(
    ! [A_107,B_108] : k5_xboole_0(k5_xboole_0(A_107,B_108),k3_xboole_0(A_107,B_108)) = k2_xboole_0(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6111,plain,(
    ! [A_215,B_216] : k5_xboole_0(k5_xboole_0(A_215,B_216),k3_xboole_0(B_216,A_215)) = k2_xboole_0(A_215,B_216) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1193])).

tff(c_22,plain,(
    ! [A_20,B_21,C_22] : k5_xboole_0(k5_xboole_0(A_20,B_21),C_22) = k5_xboole_0(A_20,k5_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6133,plain,(
    ! [A_215,B_216] : k5_xboole_0(A_215,k5_xboole_0(B_216,k3_xboole_0(B_216,A_215))) = k2_xboole_0(A_215,B_216) ),
    inference(superposition,[status(thm),theory(equality)],[c_6111,c_22])).

tff(c_6233,plain,(
    ! [A_215,B_216] : k5_xboole_0(A_215,k4_xboole_0(B_216,A_215)) = k2_xboole_0(A_215,B_216) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6133])).

tff(c_181,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(k1_tarski(A_59),B_60)
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4365,plain,(
    ! [A_186,B_187] :
      ( k3_xboole_0(k1_tarski(A_186),B_187) = k1_tarski(A_186)
      | ~ r2_hidden(A_186,B_187) ) ),
    inference(resolution,[status(thm)],[c_181,c_12])).

tff(c_28475,plain,(
    ! [B_397,A_398] :
      ( k3_xboole_0(B_397,k1_tarski(A_398)) = k1_tarski(A_398)
      | ~ r2_hidden(A_398,B_397) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4365,c_2])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_148,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2676,plain,(
    ! [A_156,B_157] : k3_xboole_0(k4_xboole_0(A_156,B_157),A_156) = k4_xboole_0(A_156,B_157) ),
    inference(resolution,[status(thm)],[c_14,c_148])).

tff(c_2744,plain,(
    ! [A_156,B_157] : k3_xboole_0(A_156,k4_xboole_0(A_156,B_157)) = k4_xboole_0(A_156,B_157) ),
    inference(superposition,[status(thm),theory(equality)],[c_2676,c_2])).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_40,plain,(
    ! [A_39] : r1_tarski(A_39,k1_zfmisc_1(k3_tarski(A_39))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_172,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_179,plain,(
    ! [A_39] : k4_xboole_0(A_39,k1_zfmisc_1(k3_tarski(A_39))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_172])).

tff(c_155,plain,(
    ! [A_39] : k3_xboole_0(A_39,k1_zfmisc_1(k3_tarski(A_39))) = A_39 ),
    inference(resolution,[status(thm)],[c_40,c_148])).

tff(c_373,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_388,plain,(
    ! [A_39] : k4_xboole_0(A_39,k1_zfmisc_1(k3_tarski(A_39))) = k5_xboole_0(A_39,A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_373])).

tff(c_399,plain,(
    ! [A_39] : k5_xboole_0(A_39,A_39) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_388])).

tff(c_747,plain,(
    ! [A_93,B_94,C_95] : k5_xboole_0(k5_xboole_0(A_93,B_94),C_95) = k5_xboole_0(A_93,k5_xboole_0(B_94,C_95)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16095,plain,(
    ! [A_314,B_315,C_316] : k5_xboole_0(A_314,k5_xboole_0(k3_xboole_0(A_314,B_315),C_316)) = k5_xboole_0(k4_xboole_0(A_314,B_315),C_316) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_747])).

tff(c_16273,plain,(
    ! [A_314,B_315] : k5_xboole_0(k4_xboole_0(A_314,B_315),k3_xboole_0(A_314,B_315)) = k5_xboole_0(A_314,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_16095])).

tff(c_16338,plain,(
    ! [A_317,B_318] : k5_xboole_0(k4_xboole_0(A_317,B_318),k3_xboole_0(A_317,B_318)) = A_317 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16273])).

tff(c_16521,plain,(
    ! [A_14,B_15] : k5_xboole_0(k3_xboole_0(A_14,B_15),k3_xboole_0(A_14,k4_xboole_0(A_14,B_15))) = A_14 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_16338])).

tff(c_16589,plain,(
    ! [A_14,B_15] : k5_xboole_0(k3_xboole_0(A_14,B_15),k4_xboole_0(A_14,B_15)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2744,c_16521])).

tff(c_28559,plain,(
    ! [A_398,B_397] :
      ( k5_xboole_0(k1_tarski(A_398),k4_xboole_0(B_397,k1_tarski(A_398))) = B_397
      | ~ r2_hidden(A_398,B_397) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28475,c_16589])).

tff(c_28872,plain,(
    ! [A_398,B_397] :
      ( k2_xboole_0(k1_tarski(A_398),B_397) = B_397
      | ~ r2_hidden(A_398,B_397) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6233,c_28559])).

tff(c_6646,plain,(
    ! [A_226,B_227] : k5_xboole_0(A_226,k5_xboole_0(B_227,k5_xboole_0(A_226,B_227))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_747,c_399])).

tff(c_400,plain,(
    ! [A_75,B_76] : k4_xboole_0(A_75,k4_xboole_0(A_75,B_76)) = k3_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_435,plain,(
    ! [A_39] : k3_xboole_0(A_39,k1_zfmisc_1(k3_tarski(A_39))) = k4_xboole_0(A_39,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_400])).

tff(c_441,plain,(
    ! [A_39] : k4_xboole_0(A_39,k1_xboole_0) = A_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_435])).

tff(c_459,plain,(
    ! [A_78] : k4_xboole_0(A_78,k1_xboole_0) = A_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_435])).

tff(c_180,plain,(
    ! [A_12,B_13] : k4_xboole_0(k4_xboole_0(A_12,B_13),A_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_172])).

tff(c_512,plain,(
    ! [A_80] : k4_xboole_0(A_80,A_80) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_180])).

tff(c_521,plain,(
    ! [A_80] : k4_xboole_0(A_80,k1_xboole_0) = k3_xboole_0(A_80,A_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_16])).

tff(c_542,plain,(
    ! [A_80] : k3_xboole_0(A_80,A_80) = A_80 ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_521])).

tff(c_1230,plain,(
    ! [A_39] : k5_xboole_0(k1_xboole_0,k3_xboole_0(A_39,A_39)) = k2_xboole_0(A_39,A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_1193])).

tff(c_1257,plain,(
    ! [A_39] : k5_xboole_0(k1_xboole_0,A_39) = k2_xboole_0(A_39,A_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_1230])).

tff(c_194,plain,(
    ! [A_61] : k4_xboole_0(A_61,k1_zfmisc_1(k3_tarski(A_61))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_172])).

tff(c_210,plain,(
    ! [A_62] : r1_tarski(k1_xboole_0,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_14])).

tff(c_218,plain,(
    ! [A_62] : k3_xboole_0(k1_xboole_0,A_62) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_210,c_12])).

tff(c_1300,plain,(
    ! [A_114] : k5_xboole_0(k1_xboole_0,A_114) = k2_xboole_0(A_114,A_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_1230])).

tff(c_24,plain,(
    ! [A_23,B_24] : k5_xboole_0(k5_xboole_0(A_23,B_24),k3_xboole_0(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1309,plain,(
    ! [A_114] : k5_xboole_0(k2_xboole_0(A_114,A_114),k3_xboole_0(k1_xboole_0,A_114)) = k2_xboole_0(k1_xboole_0,A_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_1300,c_24])).

tff(c_1458,plain,(
    ! [A_117] : k2_xboole_0(k1_xboole_0,A_117) = k2_xboole_0(A_117,A_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_218,c_1309])).

tff(c_1485,plain,(
    ! [A_39] : k5_xboole_0(k1_xboole_0,A_39) = k2_xboole_0(k1_xboole_0,A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_1257,c_1458])).

tff(c_774,plain,(
    ! [A_39,C_95] : k5_xboole_0(A_39,k5_xboole_0(A_39,C_95)) = k5_xboole_0(k1_xboole_0,C_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_747])).

tff(c_4735,plain,(
    ! [A_190,C_191] : k5_xboole_0(A_190,k5_xboole_0(A_190,C_191)) = k2_xboole_0(k1_xboole_0,C_191) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1485,c_774])).

tff(c_4796,plain,(
    ! [A_39] : k5_xboole_0(A_39,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_4735])).

tff(c_4813,plain,(
    ! [A_39] : k2_xboole_0(k1_xboole_0,A_39) = A_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4796])).

tff(c_4734,plain,(
    ! [A_39,C_95] : k5_xboole_0(A_39,k5_xboole_0(A_39,C_95)) = k2_xboole_0(k1_xboole_0,C_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1485,c_774])).

tff(c_4816,plain,(
    ! [A_39,C_95] : k5_xboole_0(A_39,k5_xboole_0(A_39,C_95)) = C_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4813,c_4734])).

tff(c_6657,plain,(
    ! [B_227,A_226] : k5_xboole_0(B_227,k5_xboole_0(A_226,B_227)) = k5_xboole_0(A_226,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6646,c_4816])).

tff(c_6759,plain,(
    ! [B_228,A_229] : k5_xboole_0(B_228,k5_xboole_0(A_229,B_228)) = A_229 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6657])).

tff(c_6771,plain,(
    ! [B_228,A_229] : k5_xboole_0(B_228,A_229) = k5_xboole_0(A_229,B_228) ),
    inference(superposition,[status(thm),theory(equality)],[c_6759,c_4816])).

tff(c_247,plain,(
    ! [A_66] : k3_xboole_0(k1_xboole_0,A_66) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_210,c_12])).

tff(c_256,plain,(
    ! [A_66] : k3_xboole_0(A_66,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_2])).

tff(c_1251,plain,(
    ! [A_19] : k5_xboole_0(A_19,k3_xboole_0(A_19,k1_xboole_0)) = k2_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1193])).

tff(c_1259,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_256,c_1251])).

tff(c_918,plain,(
    ! [A_100,B_101,C_102] : k4_xboole_0(k3_xboole_0(A_100,B_101),C_102) = k3_xboole_0(A_100,k4_xboole_0(B_101,C_102)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_676,plain,(
    ! [A_89,B_90] : r1_tarski(k3_xboole_0(A_89,B_90),A_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_14])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_704,plain,(
    ! [A_89,B_90] : k4_xboole_0(k3_xboole_0(A_89,B_90),A_89) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_676,c_6])).

tff(c_929,plain,(
    ! [C_102,B_101] : k3_xboole_0(C_102,k4_xboole_0(B_101,C_102)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_918,c_704])).

tff(c_594,plain,(
    ! [A_86,B_87,C_88] : k3_xboole_0(k3_xboole_0(A_86,B_87),C_88) = k3_xboole_0(A_86,k3_xboole_0(B_87,C_88)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7794,plain,(
    ! [A_244,B_245,C_246] : k3_xboole_0(k3_xboole_0(A_244,B_245),C_246) = k3_xboole_0(B_245,k3_xboole_0(A_244,C_246)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_594])).

tff(c_8025,plain,(
    ! [B_101,C_102,C_246] : k3_xboole_0(k4_xboole_0(B_101,C_102),k3_xboole_0(C_102,C_246)) = k3_xboole_0(k1_xboole_0,C_246) ),
    inference(superposition,[status(thm),theory(equality)],[c_929,c_7794])).

tff(c_8107,plain,(
    ! [B_101,C_102,C_246] : k3_xboole_0(k4_xboole_0(B_101,C_102),k3_xboole_0(C_102,C_246)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_8025])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] : k3_xboole_0(k3_xboole_0(A_7,B_8),C_9) = k3_xboole_0(A_7,k3_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1208,plain,(
    ! [A_23,B_24] : k5_xboole_0(k2_xboole_0(A_23,B_24),k3_xboole_0(k5_xboole_0(A_23,B_24),k3_xboole_0(A_23,B_24))) = k2_xboole_0(k5_xboole_0(A_23,B_24),k3_xboole_0(A_23,B_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1193])).

tff(c_28152,plain,(
    ! [A_395,B_396] : k5_xboole_0(k2_xboole_0(A_395,B_396),k3_xboole_0(A_395,k3_xboole_0(B_396,k5_xboole_0(A_395,B_396)))) = k2_xboole_0(k5_xboole_0(A_395,B_396),k3_xboole_0(A_395,B_396)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2,c_1208])).

tff(c_28247,plain,(
    ! [B_101,C_102] : k2_xboole_0(k5_xboole_0(k4_xboole_0(B_101,C_102),C_102),k3_xboole_0(k4_xboole_0(B_101,C_102),C_102)) = k5_xboole_0(k2_xboole_0(k4_xboole_0(B_101,C_102),C_102),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8107,c_28152])).

tff(c_28416,plain,(
    ! [B_101,C_102] : k2_xboole_0(k4_xboole_0(B_101,C_102),C_102) = k2_xboole_0(C_102,B_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6233,c_6771,c_1259,c_929,c_2,c_20,c_28247])).

tff(c_42,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_45667,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28416,c_42])).

tff(c_45888,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28872,c_45667])).

tff(c_45892,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_45888])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:20:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.90/7.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.90/7.09  
% 12.90/7.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.90/7.09  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 12.90/7.09  
% 12.90/7.09  %Foreground sorts:
% 12.90/7.09  
% 12.90/7.09  
% 12.90/7.09  %Background operators:
% 12.90/7.09  
% 12.90/7.09  
% 12.90/7.09  %Foreground operators:
% 12.90/7.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.90/7.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.90/7.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.90/7.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.90/7.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.90/7.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.90/7.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.90/7.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.90/7.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.90/7.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.90/7.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.90/7.09  tff('#skF_2', type, '#skF_2': $i).
% 12.90/7.09  tff('#skF_1', type, '#skF_1': $i).
% 12.90/7.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.90/7.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.90/7.09  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.90/7.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.90/7.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.90/7.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.90/7.09  
% 12.90/7.12  tff(f_72, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 12.90/7.12  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.90/7.12  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.90/7.12  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 12.90/7.12  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 12.90/7.12  tff(f_63, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 12.90/7.12  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.90/7.12  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 12.90/7.12  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.90/7.12  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 12.90/7.12  tff(f_67, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 12.90/7.12  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 12.90/7.12  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 12.90/7.12  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 12.90/7.12  tff(c_44, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.90/7.12  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.90/7.12  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.90/7.12  tff(c_1193, plain, (![A_107, B_108]: (k5_xboole_0(k5_xboole_0(A_107, B_108), k3_xboole_0(A_107, B_108))=k2_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.90/7.12  tff(c_6111, plain, (![A_215, B_216]: (k5_xboole_0(k5_xboole_0(A_215, B_216), k3_xboole_0(B_216, A_215))=k2_xboole_0(A_215, B_216))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1193])).
% 12.90/7.12  tff(c_22, plain, (![A_20, B_21, C_22]: (k5_xboole_0(k5_xboole_0(A_20, B_21), C_22)=k5_xboole_0(A_20, k5_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.90/7.12  tff(c_6133, plain, (![A_215, B_216]: (k5_xboole_0(A_215, k5_xboole_0(B_216, k3_xboole_0(B_216, A_215)))=k2_xboole_0(A_215, B_216))), inference(superposition, [status(thm), theory('equality')], [c_6111, c_22])).
% 12.90/7.12  tff(c_6233, plain, (![A_215, B_216]: (k5_xboole_0(A_215, k4_xboole_0(B_216, A_215))=k2_xboole_0(A_215, B_216))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_6133])).
% 12.90/7.12  tff(c_181, plain, (![A_59, B_60]: (r1_tarski(k1_tarski(A_59), B_60) | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.90/7.12  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.90/7.12  tff(c_4365, plain, (![A_186, B_187]: (k3_xboole_0(k1_tarski(A_186), B_187)=k1_tarski(A_186) | ~r2_hidden(A_186, B_187))), inference(resolution, [status(thm)], [c_181, c_12])).
% 12.90/7.12  tff(c_28475, plain, (![B_397, A_398]: (k3_xboole_0(B_397, k1_tarski(A_398))=k1_tarski(A_398) | ~r2_hidden(A_398, B_397))), inference(superposition, [status(thm), theory('equality')], [c_4365, c_2])).
% 12.90/7.12  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.90/7.12  tff(c_148, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=A_54 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.90/7.12  tff(c_2676, plain, (![A_156, B_157]: (k3_xboole_0(k4_xboole_0(A_156, B_157), A_156)=k4_xboole_0(A_156, B_157))), inference(resolution, [status(thm)], [c_14, c_148])).
% 12.90/7.12  tff(c_2744, plain, (![A_156, B_157]: (k3_xboole_0(A_156, k4_xboole_0(A_156, B_157))=k4_xboole_0(A_156, B_157))), inference(superposition, [status(thm), theory('equality')], [c_2676, c_2])).
% 12.90/7.12  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.90/7.12  tff(c_20, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.90/7.12  tff(c_40, plain, (![A_39]: (r1_tarski(A_39, k1_zfmisc_1(k3_tarski(A_39))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.90/7.12  tff(c_172, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.90/7.12  tff(c_179, plain, (![A_39]: (k4_xboole_0(A_39, k1_zfmisc_1(k3_tarski(A_39)))=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_172])).
% 12.90/7.12  tff(c_155, plain, (![A_39]: (k3_xboole_0(A_39, k1_zfmisc_1(k3_tarski(A_39)))=A_39)), inference(resolution, [status(thm)], [c_40, c_148])).
% 12.90/7.12  tff(c_373, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.90/7.12  tff(c_388, plain, (![A_39]: (k4_xboole_0(A_39, k1_zfmisc_1(k3_tarski(A_39)))=k5_xboole_0(A_39, A_39))), inference(superposition, [status(thm), theory('equality')], [c_155, c_373])).
% 12.90/7.12  tff(c_399, plain, (![A_39]: (k5_xboole_0(A_39, A_39)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_179, c_388])).
% 12.90/7.12  tff(c_747, plain, (![A_93, B_94, C_95]: (k5_xboole_0(k5_xboole_0(A_93, B_94), C_95)=k5_xboole_0(A_93, k5_xboole_0(B_94, C_95)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.90/7.12  tff(c_16095, plain, (![A_314, B_315, C_316]: (k5_xboole_0(A_314, k5_xboole_0(k3_xboole_0(A_314, B_315), C_316))=k5_xboole_0(k4_xboole_0(A_314, B_315), C_316))), inference(superposition, [status(thm), theory('equality')], [c_8, c_747])).
% 12.90/7.12  tff(c_16273, plain, (![A_314, B_315]: (k5_xboole_0(k4_xboole_0(A_314, B_315), k3_xboole_0(A_314, B_315))=k5_xboole_0(A_314, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_399, c_16095])).
% 12.90/7.12  tff(c_16338, plain, (![A_317, B_318]: (k5_xboole_0(k4_xboole_0(A_317, B_318), k3_xboole_0(A_317, B_318))=A_317)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16273])).
% 12.90/7.12  tff(c_16521, plain, (![A_14, B_15]: (k5_xboole_0(k3_xboole_0(A_14, B_15), k3_xboole_0(A_14, k4_xboole_0(A_14, B_15)))=A_14)), inference(superposition, [status(thm), theory('equality')], [c_16, c_16338])).
% 12.90/7.12  tff(c_16589, plain, (![A_14, B_15]: (k5_xboole_0(k3_xboole_0(A_14, B_15), k4_xboole_0(A_14, B_15))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_2744, c_16521])).
% 12.90/7.12  tff(c_28559, plain, (![A_398, B_397]: (k5_xboole_0(k1_tarski(A_398), k4_xboole_0(B_397, k1_tarski(A_398)))=B_397 | ~r2_hidden(A_398, B_397))), inference(superposition, [status(thm), theory('equality')], [c_28475, c_16589])).
% 12.90/7.12  tff(c_28872, plain, (![A_398, B_397]: (k2_xboole_0(k1_tarski(A_398), B_397)=B_397 | ~r2_hidden(A_398, B_397))), inference(demodulation, [status(thm), theory('equality')], [c_6233, c_28559])).
% 12.90/7.12  tff(c_6646, plain, (![A_226, B_227]: (k5_xboole_0(A_226, k5_xboole_0(B_227, k5_xboole_0(A_226, B_227)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_747, c_399])).
% 12.90/7.12  tff(c_400, plain, (![A_75, B_76]: (k4_xboole_0(A_75, k4_xboole_0(A_75, B_76))=k3_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.90/7.12  tff(c_435, plain, (![A_39]: (k3_xboole_0(A_39, k1_zfmisc_1(k3_tarski(A_39)))=k4_xboole_0(A_39, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_179, c_400])).
% 12.90/7.12  tff(c_441, plain, (![A_39]: (k4_xboole_0(A_39, k1_xboole_0)=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_155, c_435])).
% 12.90/7.12  tff(c_459, plain, (![A_78]: (k4_xboole_0(A_78, k1_xboole_0)=A_78)), inference(demodulation, [status(thm), theory('equality')], [c_155, c_435])).
% 12.90/7.12  tff(c_180, plain, (![A_12, B_13]: (k4_xboole_0(k4_xboole_0(A_12, B_13), A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_172])).
% 12.90/7.12  tff(c_512, plain, (![A_80]: (k4_xboole_0(A_80, A_80)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_459, c_180])).
% 12.90/7.12  tff(c_521, plain, (![A_80]: (k4_xboole_0(A_80, k1_xboole_0)=k3_xboole_0(A_80, A_80))), inference(superposition, [status(thm), theory('equality')], [c_512, c_16])).
% 12.90/7.12  tff(c_542, plain, (![A_80]: (k3_xboole_0(A_80, A_80)=A_80)), inference(demodulation, [status(thm), theory('equality')], [c_441, c_521])).
% 12.90/7.12  tff(c_1230, plain, (![A_39]: (k5_xboole_0(k1_xboole_0, k3_xboole_0(A_39, A_39))=k2_xboole_0(A_39, A_39))), inference(superposition, [status(thm), theory('equality')], [c_399, c_1193])).
% 12.90/7.12  tff(c_1257, plain, (![A_39]: (k5_xboole_0(k1_xboole_0, A_39)=k2_xboole_0(A_39, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_542, c_1230])).
% 12.90/7.12  tff(c_194, plain, (![A_61]: (k4_xboole_0(A_61, k1_zfmisc_1(k3_tarski(A_61)))=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_172])).
% 12.90/7.12  tff(c_210, plain, (![A_62]: (r1_tarski(k1_xboole_0, A_62))), inference(superposition, [status(thm), theory('equality')], [c_194, c_14])).
% 12.90/7.12  tff(c_218, plain, (![A_62]: (k3_xboole_0(k1_xboole_0, A_62)=k1_xboole_0)), inference(resolution, [status(thm)], [c_210, c_12])).
% 12.90/7.12  tff(c_1300, plain, (![A_114]: (k5_xboole_0(k1_xboole_0, A_114)=k2_xboole_0(A_114, A_114))), inference(demodulation, [status(thm), theory('equality')], [c_542, c_1230])).
% 12.90/7.12  tff(c_24, plain, (![A_23, B_24]: (k5_xboole_0(k5_xboole_0(A_23, B_24), k3_xboole_0(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.90/7.12  tff(c_1309, plain, (![A_114]: (k5_xboole_0(k2_xboole_0(A_114, A_114), k3_xboole_0(k1_xboole_0, A_114))=k2_xboole_0(k1_xboole_0, A_114))), inference(superposition, [status(thm), theory('equality')], [c_1300, c_24])).
% 12.90/7.12  tff(c_1458, plain, (![A_117]: (k2_xboole_0(k1_xboole_0, A_117)=k2_xboole_0(A_117, A_117))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_218, c_1309])).
% 12.90/7.12  tff(c_1485, plain, (![A_39]: (k5_xboole_0(k1_xboole_0, A_39)=k2_xboole_0(k1_xboole_0, A_39))), inference(superposition, [status(thm), theory('equality')], [c_1257, c_1458])).
% 12.90/7.12  tff(c_774, plain, (![A_39, C_95]: (k5_xboole_0(A_39, k5_xboole_0(A_39, C_95))=k5_xboole_0(k1_xboole_0, C_95))), inference(superposition, [status(thm), theory('equality')], [c_399, c_747])).
% 12.90/7.12  tff(c_4735, plain, (![A_190, C_191]: (k5_xboole_0(A_190, k5_xboole_0(A_190, C_191))=k2_xboole_0(k1_xboole_0, C_191))), inference(demodulation, [status(thm), theory('equality')], [c_1485, c_774])).
% 12.90/7.12  tff(c_4796, plain, (![A_39]: (k5_xboole_0(A_39, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_39))), inference(superposition, [status(thm), theory('equality')], [c_399, c_4735])).
% 12.90/7.12  tff(c_4813, plain, (![A_39]: (k2_xboole_0(k1_xboole_0, A_39)=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4796])).
% 12.90/7.12  tff(c_4734, plain, (![A_39, C_95]: (k5_xboole_0(A_39, k5_xboole_0(A_39, C_95))=k2_xboole_0(k1_xboole_0, C_95))), inference(demodulation, [status(thm), theory('equality')], [c_1485, c_774])).
% 12.90/7.12  tff(c_4816, plain, (![A_39, C_95]: (k5_xboole_0(A_39, k5_xboole_0(A_39, C_95))=C_95)), inference(demodulation, [status(thm), theory('equality')], [c_4813, c_4734])).
% 12.90/7.12  tff(c_6657, plain, (![B_227, A_226]: (k5_xboole_0(B_227, k5_xboole_0(A_226, B_227))=k5_xboole_0(A_226, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6646, c_4816])).
% 12.90/7.12  tff(c_6759, plain, (![B_228, A_229]: (k5_xboole_0(B_228, k5_xboole_0(A_229, B_228))=A_229)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_6657])).
% 12.90/7.12  tff(c_6771, plain, (![B_228, A_229]: (k5_xboole_0(B_228, A_229)=k5_xboole_0(A_229, B_228))), inference(superposition, [status(thm), theory('equality')], [c_6759, c_4816])).
% 12.90/7.12  tff(c_247, plain, (![A_66]: (k3_xboole_0(k1_xboole_0, A_66)=k1_xboole_0)), inference(resolution, [status(thm)], [c_210, c_12])).
% 12.90/7.12  tff(c_256, plain, (![A_66]: (k3_xboole_0(A_66, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_247, c_2])).
% 12.90/7.12  tff(c_1251, plain, (![A_19]: (k5_xboole_0(A_19, k3_xboole_0(A_19, k1_xboole_0))=k2_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1193])).
% 12.90/7.12  tff(c_1259, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_256, c_1251])).
% 12.90/7.12  tff(c_918, plain, (![A_100, B_101, C_102]: (k4_xboole_0(k3_xboole_0(A_100, B_101), C_102)=k3_xboole_0(A_100, k4_xboole_0(B_101, C_102)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.90/7.12  tff(c_676, plain, (![A_89, B_90]: (r1_tarski(k3_xboole_0(A_89, B_90), A_89))), inference(superposition, [status(thm), theory('equality')], [c_400, c_14])).
% 12.90/7.12  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.90/7.12  tff(c_704, plain, (![A_89, B_90]: (k4_xboole_0(k3_xboole_0(A_89, B_90), A_89)=k1_xboole_0)), inference(resolution, [status(thm)], [c_676, c_6])).
% 12.90/7.12  tff(c_929, plain, (![C_102, B_101]: (k3_xboole_0(C_102, k4_xboole_0(B_101, C_102))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_918, c_704])).
% 12.90/7.12  tff(c_594, plain, (![A_86, B_87, C_88]: (k3_xboole_0(k3_xboole_0(A_86, B_87), C_88)=k3_xboole_0(A_86, k3_xboole_0(B_87, C_88)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.90/7.12  tff(c_7794, plain, (![A_244, B_245, C_246]: (k3_xboole_0(k3_xboole_0(A_244, B_245), C_246)=k3_xboole_0(B_245, k3_xboole_0(A_244, C_246)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_594])).
% 12.90/7.12  tff(c_8025, plain, (![B_101, C_102, C_246]: (k3_xboole_0(k4_xboole_0(B_101, C_102), k3_xboole_0(C_102, C_246))=k3_xboole_0(k1_xboole_0, C_246))), inference(superposition, [status(thm), theory('equality')], [c_929, c_7794])).
% 12.90/7.12  tff(c_8107, plain, (![B_101, C_102, C_246]: (k3_xboole_0(k4_xboole_0(B_101, C_102), k3_xboole_0(C_102, C_246))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_218, c_8025])).
% 12.90/7.12  tff(c_10, plain, (![A_7, B_8, C_9]: (k3_xboole_0(k3_xboole_0(A_7, B_8), C_9)=k3_xboole_0(A_7, k3_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.90/7.12  tff(c_1208, plain, (![A_23, B_24]: (k5_xboole_0(k2_xboole_0(A_23, B_24), k3_xboole_0(k5_xboole_0(A_23, B_24), k3_xboole_0(A_23, B_24)))=k2_xboole_0(k5_xboole_0(A_23, B_24), k3_xboole_0(A_23, B_24)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1193])).
% 12.90/7.12  tff(c_28152, plain, (![A_395, B_396]: (k5_xboole_0(k2_xboole_0(A_395, B_396), k3_xboole_0(A_395, k3_xboole_0(B_396, k5_xboole_0(A_395, B_396))))=k2_xboole_0(k5_xboole_0(A_395, B_396), k3_xboole_0(A_395, B_396)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2, c_1208])).
% 12.90/7.12  tff(c_28247, plain, (![B_101, C_102]: (k2_xboole_0(k5_xboole_0(k4_xboole_0(B_101, C_102), C_102), k3_xboole_0(k4_xboole_0(B_101, C_102), C_102))=k5_xboole_0(k2_xboole_0(k4_xboole_0(B_101, C_102), C_102), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8107, c_28152])).
% 12.90/7.12  tff(c_28416, plain, (![B_101, C_102]: (k2_xboole_0(k4_xboole_0(B_101, C_102), C_102)=k2_xboole_0(C_102, B_101))), inference(demodulation, [status(thm), theory('equality')], [c_6233, c_6771, c_1259, c_929, c_2, c_20, c_28247])).
% 12.90/7.12  tff(c_42, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.90/7.12  tff(c_45667, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28416, c_42])).
% 12.90/7.12  tff(c_45888, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_28872, c_45667])).
% 12.90/7.12  tff(c_45892, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_45888])).
% 12.90/7.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.90/7.12  
% 12.90/7.12  Inference rules
% 12.90/7.12  ----------------------
% 12.90/7.12  #Ref     : 0
% 12.90/7.12  #Sup     : 11435
% 12.90/7.12  #Fact    : 0
% 12.90/7.12  #Define  : 0
% 12.90/7.12  #Split   : 1
% 12.90/7.12  #Chain   : 0
% 12.90/7.12  #Close   : 0
% 12.90/7.12  
% 12.90/7.12  Ordering : KBO
% 12.90/7.12  
% 12.90/7.12  Simplification rules
% 12.90/7.12  ----------------------
% 12.90/7.12  #Subsume      : 239
% 12.90/7.12  #Demod        : 14583
% 12.90/7.12  #Tautology    : 7174
% 12.90/7.12  #SimpNegUnit  : 0
% 12.90/7.12  #BackRed      : 20
% 12.90/7.12  
% 12.90/7.12  #Partial instantiations: 0
% 12.90/7.12  #Strategies tried      : 1
% 12.90/7.12  
% 12.90/7.12  Timing (in seconds)
% 12.90/7.12  ----------------------
% 12.90/7.12  Preprocessing        : 0.30
% 12.90/7.12  Parsing              : 0.16
% 12.90/7.12  CNF conversion       : 0.02
% 12.90/7.12  Main loop            : 5.90
% 12.90/7.12  Inferencing          : 0.86
% 12.90/7.12  Reduction            : 3.83
% 12.90/7.12  Demodulation         : 3.52
% 12.90/7.12  BG Simplification    : 0.12
% 12.90/7.12  Subsumption          : 0.84
% 12.90/7.12  Abstraction          : 0.21
% 12.90/7.12  MUC search           : 0.00
% 12.90/7.12  Cooper               : 0.00
% 12.90/7.12  Total                : 6.24
% 12.90/7.12  Index Insertion      : 0.00
% 12.90/7.12  Index Deletion       : 0.00
% 12.90/7.12  Index Matching       : 0.00
% 12.90/7.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
