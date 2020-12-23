%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:37 EST 2020

% Result     : Theorem 6.73s
% Output     : CNFRefutation 7.06s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 896 expanded)
%              Number of leaves         :   31 ( 313 expanded)
%              Depth                    :   18
%              Number of atoms          :   83 (1008 expanded)
%              Number of equality atoms :   64 ( 750 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_40,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_318,plain,(
    ! [A_61,B_62] : k5_xboole_0(A_61,k3_xboole_0(A_61,B_62)) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_339,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_318])).

tff(c_762,plain,(
    ! [A_90,B_91] : k5_xboole_0(k5_xboole_0(A_90,B_91),k3_xboole_0(A_90,B_91)) = k2_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] : k5_xboole_0(k5_xboole_0(A_13,B_14),C_15) = k5_xboole_0(A_13,k5_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_777,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k5_xboole_0(B_91,k3_xboole_0(A_90,B_91))) = k2_xboole_0(A_90,B_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_18])).

tff(c_826,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k4_xboole_0(B_91,A_90)) = k2_xboole_0(A_90,B_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_777])).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_106,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_119,plain,(
    ! [A_46] : k3_xboole_0(k1_xboole_0,A_46) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_106])).

tff(c_124,plain,(
    ! [A_46] : k3_xboole_0(A_46,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_2])).

tff(c_330,plain,(
    ! [A_46] : k5_xboole_0(A_46,k1_xboole_0) = k4_xboole_0(A_46,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_318])).

tff(c_343,plain,(
    ! [A_46] : k5_xboole_0(A_46,k1_xboole_0) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_330])).

tff(c_531,plain,(
    ! [A_81,B_82,C_83] : k5_xboole_0(k5_xboole_0(A_81,B_82),C_83) = k5_xboole_0(A_81,k5_xboole_0(B_82,C_83)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ! [A_32] : r1_tarski(A_32,k1_zfmisc_1(k3_tarski(A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_204,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_215,plain,(
    ! [A_32] : k4_xboole_0(A_32,k1_zfmisc_1(k3_tarski(A_32))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_204])).

tff(c_117,plain,(
    ! [A_32] : k3_xboole_0(A_32,k1_zfmisc_1(k3_tarski(A_32))) = A_32 ),
    inference(resolution,[status(thm)],[c_36,c_106])).

tff(c_327,plain,(
    ! [A_32] : k4_xboole_0(A_32,k1_zfmisc_1(k3_tarski(A_32))) = k5_xboole_0(A_32,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_318])).

tff(c_342,plain,(
    ! [A_32] : k5_xboole_0(A_32,A_32) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_327])).

tff(c_549,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k5_xboole_0(B_82,k5_xboole_0(A_81,B_82))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_342])).

tff(c_937,plain,(
    ! [A_98,B_99] : k5_xboole_0(A_98,k4_xboole_0(B_99,A_98)) = k2_xboole_0(A_98,B_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_777])).

tff(c_982,plain,(
    ! [A_12] : k5_xboole_0(k1_xboole_0,A_12) = k2_xboole_0(k1_xboole_0,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_937])).

tff(c_576,plain,(
    ! [A_32,C_83] : k5_xboole_0(A_32,k5_xboole_0(A_32,C_83)) = k5_xboole_0(k1_xboole_0,C_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_531])).

tff(c_1291,plain,(
    ! [A_106,C_107] : k5_xboole_0(A_106,k5_xboole_0(A_106,C_107)) = k2_xboole_0(k1_xboole_0,C_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_982,c_576])).

tff(c_1370,plain,(
    ! [A_32] : k5_xboole_0(A_32,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_1291])).

tff(c_1389,plain,(
    ! [A_32] : k2_xboole_0(k1_xboole_0,A_32) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_1370])).

tff(c_1290,plain,(
    ! [A_32,C_83] : k5_xboole_0(A_32,k5_xboole_0(A_32,C_83)) = k2_xboole_0(k1_xboole_0,C_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_982,c_576])).

tff(c_1533,plain,(
    ! [A_110,C_111] : k5_xboole_0(A_110,k5_xboole_0(A_110,C_111)) = C_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1389,c_1290])).

tff(c_1589,plain,(
    ! [B_82,A_81] : k5_xboole_0(B_82,k5_xboole_0(A_81,B_82)) = k5_xboole_0(A_81,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_1533])).

tff(c_1854,plain,(
    ! [B_117,A_118] : k5_xboole_0(B_117,k5_xboole_0(A_118,B_117)) = A_118 ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_1589])).

tff(c_1390,plain,(
    ! [A_32,C_83] : k5_xboole_0(A_32,k5_xboole_0(A_32,C_83)) = C_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1389,c_1290])).

tff(c_1866,plain,(
    ! [B_117,A_118] : k5_xboole_0(B_117,A_118) = k5_xboole_0(A_118,B_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_1854,c_1390])).

tff(c_32,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k1_tarski(A_28),B_29)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_116,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(k1_tarski(A_28),B_29) = k1_tarski(A_28)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_32,c_106])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2437,plain,(
    ! [A_128,B_129,C_130] : k5_xboole_0(A_128,k5_xboole_0(k3_xboole_0(A_128,B_129),C_130)) = k5_xboole_0(k4_xboole_0(A_128,B_129),C_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_531])).

tff(c_2537,plain,(
    ! [A_128,B_129] : k5_xboole_0(k4_xboole_0(A_128,B_129),k3_xboole_0(A_128,B_129)) = k5_xboole_0(A_128,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_2437])).

tff(c_2570,plain,(
    ! [A_131,B_132] : k5_xboole_0(k4_xboole_0(A_131,B_132),k3_xboole_0(A_131,B_132)) = A_131 ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_2537])).

tff(c_2678,plain,(
    ! [B_133,A_134] : k5_xboole_0(k4_xboole_0(B_133,A_134),k3_xboole_0(A_134,B_133)) = B_133 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2570])).

tff(c_2734,plain,(
    ! [B_29,A_28] :
      ( k5_xboole_0(k4_xboole_0(B_29,k1_tarski(A_28)),k1_tarski(A_28)) = B_29
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_2678])).

tff(c_2780,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(k1_tarski(A_28),B_29) = B_29
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_826,c_1866,c_2734])).

tff(c_1583,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k2_xboole_0(A_90,B_91)) = k4_xboole_0(B_91,A_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_826,c_1533])).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3628,plain,(
    ! [A_147,B_148] : k5_xboole_0(A_147,k2_xboole_0(A_147,B_148)) = k4_xboole_0(B_148,A_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_826,c_1533])).

tff(c_3706,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k4_xboole_0(k4_xboole_0(B_11,A_10),A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3628])).

tff(c_4806,plain,(
    ! [B_166,A_167] : k4_xboole_0(k4_xboole_0(B_166,A_167),A_167) = k4_xboole_0(B_166,A_167) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1583,c_3706])).

tff(c_1612,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1533])).

tff(c_4827,plain,(
    ! [B_166,A_167] : k5_xboole_0(k4_xboole_0(B_166,A_167),k4_xboole_0(B_166,A_167)) = k3_xboole_0(k4_xboole_0(B_166,A_167),A_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_4806,c_1612])).

tff(c_4890,plain,(
    ! [A_167,B_166] : k3_xboole_0(A_167,k4_xboole_0(B_166,A_167)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_2,c_4827])).

tff(c_6496,plain,(
    ! [B_187,A_188] : k5_xboole_0(k4_xboole_0(B_187,A_188),k2_xboole_0(A_188,B_187)) = A_188 ),
    inference(superposition,[status(thm),theory(equality)],[c_826,c_1854])).

tff(c_6644,plain,(
    ! [B_189,A_190] : k5_xboole_0(k4_xboole_0(B_189,A_190),A_190) = k2_xboole_0(A_190,B_189) ),
    inference(superposition,[status(thm),theory(equality)],[c_6496,c_1390])).

tff(c_20,plain,(
    ! [A_16,B_17] : k5_xboole_0(k5_xboole_0(A_16,B_17),k3_xboole_0(A_16,B_17)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6698,plain,(
    ! [A_190,B_189] : k5_xboole_0(k2_xboole_0(A_190,B_189),k3_xboole_0(k4_xboole_0(B_189,A_190),A_190)) = k2_xboole_0(k4_xboole_0(B_189,A_190),A_190) ),
    inference(superposition,[status(thm),theory(equality)],[c_6644,c_20])).

tff(c_6774,plain,(
    ! [B_189,A_190] : k2_xboole_0(k4_xboole_0(B_189,A_190),A_190) = k2_xboole_0(A_190,B_189) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_4890,c_2,c_6698])).

tff(c_38,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8535,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6774,c_38])).

tff(c_8643,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2780,c_8535])).

tff(c_8647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8643])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.73/2.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.73/2.73  
% 6.73/2.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.73/2.73  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 6.73/2.73  
% 6.73/2.73  %Foreground sorts:
% 6.73/2.73  
% 6.73/2.73  
% 6.73/2.73  %Background operators:
% 6.73/2.73  
% 6.73/2.73  
% 6.73/2.73  %Foreground operators:
% 6.73/2.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.73/2.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.73/2.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.73/2.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.73/2.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.73/2.73  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.73/2.73  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.73/2.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.73/2.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.73/2.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.73/2.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.73/2.73  tff('#skF_2', type, '#skF_2': $i).
% 6.73/2.73  tff('#skF_1', type, '#skF_1': $i).
% 6.73/2.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.73/2.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.73/2.73  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.73/2.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.73/2.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.73/2.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.73/2.73  
% 7.06/2.75  tff(f_68, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 7.06/2.75  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.06/2.75  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.06/2.75  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 7.06/2.75  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.06/2.75  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.06/2.75  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.06/2.75  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.06/2.75  tff(f_63, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 7.06/2.75  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.06/2.75  tff(f_59, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 7.06/2.75  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.06/2.75  tff(c_40, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.06/2.75  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.06/2.75  tff(c_318, plain, (![A_61, B_62]: (k5_xboole_0(A_61, k3_xboole_0(A_61, B_62))=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.06/2.75  tff(c_339, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_318])).
% 7.06/2.75  tff(c_762, plain, (![A_90, B_91]: (k5_xboole_0(k5_xboole_0(A_90, B_91), k3_xboole_0(A_90, B_91))=k2_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.06/2.75  tff(c_18, plain, (![A_13, B_14, C_15]: (k5_xboole_0(k5_xboole_0(A_13, B_14), C_15)=k5_xboole_0(A_13, k5_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.06/2.75  tff(c_777, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k5_xboole_0(B_91, k3_xboole_0(A_90, B_91)))=k2_xboole_0(A_90, B_91))), inference(superposition, [status(thm), theory('equality')], [c_762, c_18])).
% 7.06/2.75  tff(c_826, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k4_xboole_0(B_91, A_90))=k2_xboole_0(A_90, B_91))), inference(demodulation, [status(thm), theory('equality')], [c_339, c_777])).
% 7.06/2.75  tff(c_16, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.06/2.75  tff(c_12, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.06/2.75  tff(c_106, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=A_44 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.06/2.75  tff(c_119, plain, (![A_46]: (k3_xboole_0(k1_xboole_0, A_46)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_106])).
% 7.06/2.75  tff(c_124, plain, (![A_46]: (k3_xboole_0(A_46, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_119, c_2])).
% 7.06/2.75  tff(c_330, plain, (![A_46]: (k5_xboole_0(A_46, k1_xboole_0)=k4_xboole_0(A_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_124, c_318])).
% 7.06/2.75  tff(c_343, plain, (![A_46]: (k5_xboole_0(A_46, k1_xboole_0)=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_330])).
% 7.06/2.75  tff(c_531, plain, (![A_81, B_82, C_83]: (k5_xboole_0(k5_xboole_0(A_81, B_82), C_83)=k5_xboole_0(A_81, k5_xboole_0(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.06/2.75  tff(c_36, plain, (![A_32]: (r1_tarski(A_32, k1_zfmisc_1(k3_tarski(A_32))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.06/2.75  tff(c_204, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.06/2.75  tff(c_215, plain, (![A_32]: (k4_xboole_0(A_32, k1_zfmisc_1(k3_tarski(A_32)))=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_204])).
% 7.06/2.75  tff(c_117, plain, (![A_32]: (k3_xboole_0(A_32, k1_zfmisc_1(k3_tarski(A_32)))=A_32)), inference(resolution, [status(thm)], [c_36, c_106])).
% 7.06/2.75  tff(c_327, plain, (![A_32]: (k4_xboole_0(A_32, k1_zfmisc_1(k3_tarski(A_32)))=k5_xboole_0(A_32, A_32))), inference(superposition, [status(thm), theory('equality')], [c_117, c_318])).
% 7.06/2.75  tff(c_342, plain, (![A_32]: (k5_xboole_0(A_32, A_32)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_215, c_327])).
% 7.06/2.75  tff(c_549, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k5_xboole_0(B_82, k5_xboole_0(A_81, B_82)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_531, c_342])).
% 7.06/2.75  tff(c_937, plain, (![A_98, B_99]: (k5_xboole_0(A_98, k4_xboole_0(B_99, A_98))=k2_xboole_0(A_98, B_99))), inference(demodulation, [status(thm), theory('equality')], [c_339, c_777])).
% 7.06/2.75  tff(c_982, plain, (![A_12]: (k5_xboole_0(k1_xboole_0, A_12)=k2_xboole_0(k1_xboole_0, A_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_937])).
% 7.06/2.75  tff(c_576, plain, (![A_32, C_83]: (k5_xboole_0(A_32, k5_xboole_0(A_32, C_83))=k5_xboole_0(k1_xboole_0, C_83))), inference(superposition, [status(thm), theory('equality')], [c_342, c_531])).
% 7.06/2.75  tff(c_1291, plain, (![A_106, C_107]: (k5_xboole_0(A_106, k5_xboole_0(A_106, C_107))=k2_xboole_0(k1_xboole_0, C_107))), inference(demodulation, [status(thm), theory('equality')], [c_982, c_576])).
% 7.06/2.75  tff(c_1370, plain, (![A_32]: (k5_xboole_0(A_32, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_32))), inference(superposition, [status(thm), theory('equality')], [c_342, c_1291])).
% 7.06/2.75  tff(c_1389, plain, (![A_32]: (k2_xboole_0(k1_xboole_0, A_32)=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_343, c_1370])).
% 7.06/2.75  tff(c_1290, plain, (![A_32, C_83]: (k5_xboole_0(A_32, k5_xboole_0(A_32, C_83))=k2_xboole_0(k1_xboole_0, C_83))), inference(demodulation, [status(thm), theory('equality')], [c_982, c_576])).
% 7.06/2.75  tff(c_1533, plain, (![A_110, C_111]: (k5_xboole_0(A_110, k5_xboole_0(A_110, C_111))=C_111)), inference(demodulation, [status(thm), theory('equality')], [c_1389, c_1290])).
% 7.06/2.75  tff(c_1589, plain, (![B_82, A_81]: (k5_xboole_0(B_82, k5_xboole_0(A_81, B_82))=k5_xboole_0(A_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_549, c_1533])).
% 7.06/2.75  tff(c_1854, plain, (![B_117, A_118]: (k5_xboole_0(B_117, k5_xboole_0(A_118, B_117))=A_118)), inference(demodulation, [status(thm), theory('equality')], [c_343, c_1589])).
% 7.06/2.75  tff(c_1390, plain, (![A_32, C_83]: (k5_xboole_0(A_32, k5_xboole_0(A_32, C_83))=C_83)), inference(demodulation, [status(thm), theory('equality')], [c_1389, c_1290])).
% 7.06/2.75  tff(c_1866, plain, (![B_117, A_118]: (k5_xboole_0(B_117, A_118)=k5_xboole_0(A_118, B_117))), inference(superposition, [status(thm), theory('equality')], [c_1854, c_1390])).
% 7.06/2.75  tff(c_32, plain, (![A_28, B_29]: (r1_tarski(k1_tarski(A_28), B_29) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.06/2.75  tff(c_116, plain, (![A_28, B_29]: (k3_xboole_0(k1_tarski(A_28), B_29)=k1_tarski(A_28) | ~r2_hidden(A_28, B_29))), inference(resolution, [status(thm)], [c_32, c_106])).
% 7.06/2.75  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.06/2.75  tff(c_2437, plain, (![A_128, B_129, C_130]: (k5_xboole_0(A_128, k5_xboole_0(k3_xboole_0(A_128, B_129), C_130))=k5_xboole_0(k4_xboole_0(A_128, B_129), C_130))), inference(superposition, [status(thm), theory('equality')], [c_8, c_531])).
% 7.06/2.75  tff(c_2537, plain, (![A_128, B_129]: (k5_xboole_0(k4_xboole_0(A_128, B_129), k3_xboole_0(A_128, B_129))=k5_xboole_0(A_128, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_342, c_2437])).
% 7.06/2.75  tff(c_2570, plain, (![A_131, B_132]: (k5_xboole_0(k4_xboole_0(A_131, B_132), k3_xboole_0(A_131, B_132))=A_131)), inference(demodulation, [status(thm), theory('equality')], [c_343, c_2537])).
% 7.06/2.75  tff(c_2678, plain, (![B_133, A_134]: (k5_xboole_0(k4_xboole_0(B_133, A_134), k3_xboole_0(A_134, B_133))=B_133)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2570])).
% 7.06/2.75  tff(c_2734, plain, (![B_29, A_28]: (k5_xboole_0(k4_xboole_0(B_29, k1_tarski(A_28)), k1_tarski(A_28))=B_29 | ~r2_hidden(A_28, B_29))), inference(superposition, [status(thm), theory('equality')], [c_116, c_2678])).
% 7.06/2.75  tff(c_2780, plain, (![A_28, B_29]: (k2_xboole_0(k1_tarski(A_28), B_29)=B_29 | ~r2_hidden(A_28, B_29))), inference(demodulation, [status(thm), theory('equality')], [c_826, c_1866, c_2734])).
% 7.06/2.75  tff(c_1583, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k2_xboole_0(A_90, B_91))=k4_xboole_0(B_91, A_90))), inference(superposition, [status(thm), theory('equality')], [c_826, c_1533])).
% 7.06/2.75  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.06/2.75  tff(c_3628, plain, (![A_147, B_148]: (k5_xboole_0(A_147, k2_xboole_0(A_147, B_148))=k4_xboole_0(B_148, A_147))), inference(superposition, [status(thm), theory('equality')], [c_826, c_1533])).
% 7.06/2.75  tff(c_3706, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k4_xboole_0(k4_xboole_0(B_11, A_10), A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3628])).
% 7.06/2.75  tff(c_4806, plain, (![B_166, A_167]: (k4_xboole_0(k4_xboole_0(B_166, A_167), A_167)=k4_xboole_0(B_166, A_167))), inference(demodulation, [status(thm), theory('equality')], [c_1583, c_3706])).
% 7.06/2.75  tff(c_1612, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1533])).
% 7.06/2.75  tff(c_4827, plain, (![B_166, A_167]: (k5_xboole_0(k4_xboole_0(B_166, A_167), k4_xboole_0(B_166, A_167))=k3_xboole_0(k4_xboole_0(B_166, A_167), A_167))), inference(superposition, [status(thm), theory('equality')], [c_4806, c_1612])).
% 7.06/2.75  tff(c_4890, plain, (![A_167, B_166]: (k3_xboole_0(A_167, k4_xboole_0(B_166, A_167))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_342, c_2, c_4827])).
% 7.06/2.75  tff(c_6496, plain, (![B_187, A_188]: (k5_xboole_0(k4_xboole_0(B_187, A_188), k2_xboole_0(A_188, B_187))=A_188)), inference(superposition, [status(thm), theory('equality')], [c_826, c_1854])).
% 7.06/2.75  tff(c_6644, plain, (![B_189, A_190]: (k5_xboole_0(k4_xboole_0(B_189, A_190), A_190)=k2_xboole_0(A_190, B_189))), inference(superposition, [status(thm), theory('equality')], [c_6496, c_1390])).
% 7.06/2.75  tff(c_20, plain, (![A_16, B_17]: (k5_xboole_0(k5_xboole_0(A_16, B_17), k3_xboole_0(A_16, B_17))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.06/2.75  tff(c_6698, plain, (![A_190, B_189]: (k5_xboole_0(k2_xboole_0(A_190, B_189), k3_xboole_0(k4_xboole_0(B_189, A_190), A_190))=k2_xboole_0(k4_xboole_0(B_189, A_190), A_190))), inference(superposition, [status(thm), theory('equality')], [c_6644, c_20])).
% 7.06/2.75  tff(c_6774, plain, (![B_189, A_190]: (k2_xboole_0(k4_xboole_0(B_189, A_190), A_190)=k2_xboole_0(A_190, B_189))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_4890, c_2, c_6698])).
% 7.06/2.75  tff(c_38, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.06/2.75  tff(c_8535, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6774, c_38])).
% 7.06/2.75  tff(c_8643, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2780, c_8535])).
% 7.06/2.75  tff(c_8647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_8643])).
% 7.06/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.06/2.75  
% 7.06/2.75  Inference rules
% 7.06/2.75  ----------------------
% 7.06/2.75  #Ref     : 0
% 7.06/2.75  #Sup     : 2135
% 7.06/2.75  #Fact    : 0
% 7.06/2.75  #Define  : 0
% 7.06/2.75  #Split   : 1
% 7.06/2.75  #Chain   : 0
% 7.06/2.75  #Close   : 0
% 7.06/2.75  
% 7.06/2.75  Ordering : KBO
% 7.06/2.75  
% 7.06/2.75  Simplification rules
% 7.06/2.75  ----------------------
% 7.06/2.75  #Subsume      : 74
% 7.06/2.75  #Demod        : 2492
% 7.06/2.75  #Tautology    : 1118
% 7.06/2.75  #SimpNegUnit  : 0
% 7.06/2.75  #BackRed      : 7
% 7.06/2.75  
% 7.06/2.75  #Partial instantiations: 0
% 7.06/2.75  #Strategies tried      : 1
% 7.06/2.75  
% 7.06/2.75  Timing (in seconds)
% 7.06/2.75  ----------------------
% 7.06/2.75  Preprocessing        : 0.33
% 7.06/2.75  Parsing              : 0.18
% 7.06/2.75  CNF conversion       : 0.02
% 7.06/2.75  Main loop            : 1.59
% 7.06/2.75  Inferencing          : 0.40
% 7.06/2.75  Reduction            : 0.86
% 7.06/2.75  Demodulation         : 0.74
% 7.06/2.75  BG Simplification    : 0.06
% 7.06/2.75  Subsumption          : 0.19
% 7.06/2.75  Abstraction          : 0.09
% 7.06/2.75  MUC search           : 0.00
% 7.06/2.75  Cooper               : 0.00
% 7.06/2.75  Total                : 1.96
% 7.06/2.75  Index Insertion      : 0.00
% 7.06/2.75  Index Deletion       : 0.00
% 7.06/2.75  Index Matching       : 0.00
% 7.06/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
