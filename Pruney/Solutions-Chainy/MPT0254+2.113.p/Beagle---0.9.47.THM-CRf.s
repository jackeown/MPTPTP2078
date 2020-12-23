%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:33 EST 2020

% Result     : Theorem 4.46s
% Output     : CNFRefutation 4.74s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 663 expanded)
%              Number of leaves         :   36 ( 248 expanded)
%              Depth                    :   14
%              Number of atoms          :   70 ( 753 expanded)
%              Number of equality atoms :   57 ( 563 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_16,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_22] : k5_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_266,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k3_xboole_0(A_75,B_76)) = k4_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_289,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_266])).

tff(c_294,plain,(
    ! [A_77] : k4_xboole_0(A_77,A_77) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_289])).

tff(c_18,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_299,plain,(
    ! [A_77] : r1_xboole_0(k1_xboole_0,A_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_18])).

tff(c_12,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_304,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r1_xboole_0(A_78,B_79)
      | ~ r2_hidden(C_80,k3_xboole_0(A_78,B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_421,plain,(
    ! [A_94,B_95] :
      ( ~ r1_xboole_0(A_94,B_95)
      | k3_xboole_0(A_94,B_95) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_304])).

tff(c_441,plain,(
    ! [A_96] : k3_xboole_0(k1_xboole_0,A_96) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_299,c_421])).

tff(c_701,plain,(
    ! [A_106] : k3_xboole_0(A_106,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_441])).

tff(c_24,plain,(
    ! [A_23,B_24] : k5_xboole_0(k5_xboole_0(A_23,B_24),k3_xboole_0(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_706,plain,(
    ! [A_106] : k5_xboole_0(k5_xboole_0(A_106,k1_xboole_0),k1_xboole_0) = k2_xboole_0(A_106,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_701,c_24])).

tff(c_744,plain,(
    ! [A_106] : k2_xboole_0(A_106,k1_xboole_0) = A_106 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_706])).

tff(c_436,plain,(
    ! [A_77] : k3_xboole_0(k1_xboole_0,A_77) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_299,c_421])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_14,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_589,plain,(
    ! [A_102,B_103,C_104] : k5_xboole_0(k5_xboole_0(A_102,B_103),C_104) = k5_xboole_0(A_102,k5_xboole_0(B_103,C_104)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2449,plain,(
    ! [B_180,A_181,C_182] : k5_xboole_0(k5_xboole_0(B_180,A_181),C_182) = k5_xboole_0(A_181,k5_xboole_0(B_180,C_182)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_589])).

tff(c_2511,plain,(
    ! [A_181,B_180] : k5_xboole_0(A_181,k5_xboole_0(B_180,k3_xboole_0(B_180,A_181))) = k2_xboole_0(B_180,A_181) ),
    inference(superposition,[status(thm),theory(equality)],[c_2449,c_24])).

tff(c_2674,plain,(
    ! [A_183,B_184] : k5_xboole_0(A_183,k4_xboole_0(B_184,A_183)) = k2_xboole_0(B_184,A_183) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2511])).

tff(c_96,plain,(
    ! [B_63,A_64] : k5_xboole_0(B_63,A_64) = k5_xboole_0(A_64,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_112,plain,(
    ! [A_64] : k5_xboole_0(k1_xboole_0,A_64) = A_64 ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_16])).

tff(c_666,plain,(
    ! [A_22,C_104] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_104)) = k5_xboole_0(k1_xboole_0,C_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_589])).

tff(c_863,plain,(
    ! [A_116,C_117] : k5_xboole_0(A_116,k5_xboole_0(A_116,C_117)) = C_117 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_666])).

tff(c_912,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_863])).

tff(c_2779,plain,(
    ! [B_185,A_186] : k5_xboole_0(k4_xboole_0(B_185,A_186),k2_xboole_0(B_185,A_186)) = A_186 ),
    inference(superposition,[status(thm),theory(equality)],[c_2674,c_912])).

tff(c_2851,plain,(
    k5_xboole_0(k4_xboole_0(k1_tarski('#skF_3'),'#skF_4'),k1_xboole_0) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2779])).

tff(c_506,plain,(
    ! [A_98,B_99] : k5_xboole_0(k5_xboole_0(A_98,B_99),k3_xboole_0(A_98,B_99)) = k2_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_518,plain,(
    ! [A_98,B_99] : k5_xboole_0(k3_xboole_0(A_98,B_99),k5_xboole_0(A_98,B_99)) = k2_xboole_0(A_98,B_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_4])).

tff(c_2869,plain,(
    k5_xboole_0(k3_xboole_0(k4_xboole_0(k1_tarski('#skF_3'),'#skF_4'),k1_xboole_0),'#skF_4') = k2_xboole_0(k4_xboole_0(k1_tarski('#skF_3'),'#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2851,c_518])).

tff(c_2908,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_744,c_16,c_436,c_4,c_2,c_2869])).

tff(c_292,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_289])).

tff(c_934,plain,(
    ! [A_118,B_119] : k3_xboole_0(k4_xboole_0(A_118,B_119),B_119) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_421])).

tff(c_951,plain,(
    ! [A_118,B_119] : k5_xboole_0(k4_xboole_0(A_118,B_119),k1_xboole_0) = k4_xboole_0(k4_xboole_0(A_118,B_119),B_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_934,c_14])).

tff(c_990,plain,(
    ! [A_118,B_119] : k4_xboole_0(k4_xboole_0(A_118,B_119),B_119) = k4_xboole_0(A_118,B_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_951])).

tff(c_2937,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k4_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2908,c_990])).

tff(c_2965,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2908,c_292,c_2937])).

tff(c_42,plain,(
    ! [B_56] : k4_xboole_0(k1_tarski(B_56),k1_tarski(B_56)) != k1_tarski(B_56) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_293,plain,(
    ! [B_56] : k1_tarski(B_56) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_42])).

tff(c_2984,plain,(
    ! [B_56] : k1_tarski(B_56) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2965,c_293])).

tff(c_3656,plain,(
    ! [A_199] : k2_xboole_0(A_199,'#skF_4') = A_199 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2965,c_744])).

tff(c_2988,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2965,c_46])).

tff(c_3662,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3656,c_2988])).

tff(c_3682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2984,c_3662])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:30:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.46/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.90  
% 4.74/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.91  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.74/1.91  
% 4.74/1.91  %Foreground sorts:
% 4.74/1.91  
% 4.74/1.91  
% 4.74/1.91  %Background operators:
% 4.74/1.91  
% 4.74/1.91  
% 4.74/1.91  %Foreground operators:
% 4.74/1.91  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.74/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.74/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.74/1.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.74/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.74/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.74/1.91  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.74/1.91  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.74/1.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.74/1.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.74/1.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.74/1.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.74/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.74/1.91  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.74/1.91  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.74/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.74/1.91  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.74/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.74/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.74/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.74/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.74/1.91  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.74/1.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.74/1.91  
% 4.74/1.92  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.74/1.92  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.74/1.92  tff(f_63, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.74/1.92  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.74/1.92  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.74/1.92  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.74/1.92  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.74/1.92  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.74/1.92  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.74/1.92  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.74/1.92  tff(f_90, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 4.74/1.92  tff(f_61, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.74/1.92  tff(f_86, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 4.74/1.92  tff(c_16, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.74/1.92  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.74/1.92  tff(c_22, plain, (![A_22]: (k5_xboole_0(A_22, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.74/1.92  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.74/1.92  tff(c_266, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k3_xboole_0(A_75, B_76))=k4_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.74/1.92  tff(c_289, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_266])).
% 4.74/1.92  tff(c_294, plain, (![A_77]: (k4_xboole_0(A_77, A_77)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_289])).
% 4.74/1.92  tff(c_18, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.74/1.92  tff(c_299, plain, (![A_77]: (r1_xboole_0(k1_xboole_0, A_77))), inference(superposition, [status(thm), theory('equality')], [c_294, c_18])).
% 4.74/1.92  tff(c_12, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.74/1.92  tff(c_304, plain, (![A_78, B_79, C_80]: (~r1_xboole_0(A_78, B_79) | ~r2_hidden(C_80, k3_xboole_0(A_78, B_79)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.74/1.92  tff(c_421, plain, (![A_94, B_95]: (~r1_xboole_0(A_94, B_95) | k3_xboole_0(A_94, B_95)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_304])).
% 4.74/1.92  tff(c_441, plain, (![A_96]: (k3_xboole_0(k1_xboole_0, A_96)=k1_xboole_0)), inference(resolution, [status(thm)], [c_299, c_421])).
% 4.74/1.92  tff(c_701, plain, (![A_106]: (k3_xboole_0(A_106, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_441])).
% 4.74/1.92  tff(c_24, plain, (![A_23, B_24]: (k5_xboole_0(k5_xboole_0(A_23, B_24), k3_xboole_0(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.74/1.92  tff(c_706, plain, (![A_106]: (k5_xboole_0(k5_xboole_0(A_106, k1_xboole_0), k1_xboole_0)=k2_xboole_0(A_106, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_701, c_24])).
% 4.74/1.92  tff(c_744, plain, (![A_106]: (k2_xboole_0(A_106, k1_xboole_0)=A_106)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_706])).
% 4.74/1.92  tff(c_436, plain, (![A_77]: (k3_xboole_0(k1_xboole_0, A_77)=k1_xboole_0)), inference(resolution, [status(thm)], [c_299, c_421])).
% 4.74/1.92  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.74/1.92  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.74/1.92  tff(c_14, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.74/1.92  tff(c_589, plain, (![A_102, B_103, C_104]: (k5_xboole_0(k5_xboole_0(A_102, B_103), C_104)=k5_xboole_0(A_102, k5_xboole_0(B_103, C_104)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.74/1.92  tff(c_2449, plain, (![B_180, A_181, C_182]: (k5_xboole_0(k5_xboole_0(B_180, A_181), C_182)=k5_xboole_0(A_181, k5_xboole_0(B_180, C_182)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_589])).
% 4.74/1.92  tff(c_2511, plain, (![A_181, B_180]: (k5_xboole_0(A_181, k5_xboole_0(B_180, k3_xboole_0(B_180, A_181)))=k2_xboole_0(B_180, A_181))), inference(superposition, [status(thm), theory('equality')], [c_2449, c_24])).
% 4.74/1.92  tff(c_2674, plain, (![A_183, B_184]: (k5_xboole_0(A_183, k4_xboole_0(B_184, A_183))=k2_xboole_0(B_184, A_183))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2511])).
% 4.74/1.92  tff(c_96, plain, (![B_63, A_64]: (k5_xboole_0(B_63, A_64)=k5_xboole_0(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.74/1.92  tff(c_112, plain, (![A_64]: (k5_xboole_0(k1_xboole_0, A_64)=A_64)), inference(superposition, [status(thm), theory('equality')], [c_96, c_16])).
% 4.74/1.92  tff(c_666, plain, (![A_22, C_104]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_104))=k5_xboole_0(k1_xboole_0, C_104))), inference(superposition, [status(thm), theory('equality')], [c_22, c_589])).
% 4.74/1.92  tff(c_863, plain, (![A_116, C_117]: (k5_xboole_0(A_116, k5_xboole_0(A_116, C_117))=C_117)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_666])).
% 4.74/1.92  tff(c_912, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_863])).
% 4.74/1.92  tff(c_2779, plain, (![B_185, A_186]: (k5_xboole_0(k4_xboole_0(B_185, A_186), k2_xboole_0(B_185, A_186))=A_186)), inference(superposition, [status(thm), theory('equality')], [c_2674, c_912])).
% 4.74/1.92  tff(c_2851, plain, (k5_xboole_0(k4_xboole_0(k1_tarski('#skF_3'), '#skF_4'), k1_xboole_0)='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_46, c_2779])).
% 4.74/1.92  tff(c_506, plain, (![A_98, B_99]: (k5_xboole_0(k5_xboole_0(A_98, B_99), k3_xboole_0(A_98, B_99))=k2_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.74/1.92  tff(c_518, plain, (![A_98, B_99]: (k5_xboole_0(k3_xboole_0(A_98, B_99), k5_xboole_0(A_98, B_99))=k2_xboole_0(A_98, B_99))), inference(superposition, [status(thm), theory('equality')], [c_506, c_4])).
% 4.74/1.92  tff(c_2869, plain, (k5_xboole_0(k3_xboole_0(k4_xboole_0(k1_tarski('#skF_3'), '#skF_4'), k1_xboole_0), '#skF_4')=k2_xboole_0(k4_xboole_0(k1_tarski('#skF_3'), '#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2851, c_518])).
% 4.74/1.92  tff(c_2908, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_744, c_16, c_436, c_4, c_2, c_2869])).
% 4.74/1.92  tff(c_292, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_289])).
% 4.74/1.92  tff(c_934, plain, (![A_118, B_119]: (k3_xboole_0(k4_xboole_0(A_118, B_119), B_119)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_421])).
% 4.74/1.92  tff(c_951, plain, (![A_118, B_119]: (k5_xboole_0(k4_xboole_0(A_118, B_119), k1_xboole_0)=k4_xboole_0(k4_xboole_0(A_118, B_119), B_119))), inference(superposition, [status(thm), theory('equality')], [c_934, c_14])).
% 4.74/1.92  tff(c_990, plain, (![A_118, B_119]: (k4_xboole_0(k4_xboole_0(A_118, B_119), B_119)=k4_xboole_0(A_118, B_119))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_951])).
% 4.74/1.92  tff(c_2937, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k4_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2908, c_990])).
% 4.74/1.92  tff(c_2965, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2908, c_292, c_2937])).
% 4.74/1.92  tff(c_42, plain, (![B_56]: (k4_xboole_0(k1_tarski(B_56), k1_tarski(B_56))!=k1_tarski(B_56))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.74/1.92  tff(c_293, plain, (![B_56]: (k1_tarski(B_56)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_292, c_42])).
% 4.74/1.92  tff(c_2984, plain, (![B_56]: (k1_tarski(B_56)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2965, c_293])).
% 4.74/1.92  tff(c_3656, plain, (![A_199]: (k2_xboole_0(A_199, '#skF_4')=A_199)), inference(demodulation, [status(thm), theory('equality')], [c_2965, c_744])).
% 4.74/1.92  tff(c_2988, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2965, c_46])).
% 4.74/1.92  tff(c_3662, plain, (k1_tarski('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3656, c_2988])).
% 4.74/1.92  tff(c_3682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2984, c_3662])).
% 4.74/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.92  
% 4.74/1.92  Inference rules
% 4.74/1.92  ----------------------
% 4.74/1.92  #Ref     : 0
% 4.74/1.92  #Sup     : 906
% 4.74/1.92  #Fact    : 0
% 4.74/1.92  #Define  : 0
% 4.74/1.92  #Split   : 0
% 4.74/1.92  #Chain   : 0
% 4.74/1.92  #Close   : 0
% 4.74/1.92  
% 4.74/1.92  Ordering : KBO
% 4.74/1.92  
% 4.74/1.92  Simplification rules
% 4.74/1.92  ----------------------
% 4.74/1.92  #Subsume      : 55
% 4.74/1.92  #Demod        : 644
% 4.74/1.92  #Tautology    : 513
% 4.74/1.92  #SimpNegUnit  : 12
% 4.74/1.92  #BackRed      : 27
% 4.74/1.92  
% 4.74/1.92  #Partial instantiations: 0
% 4.74/1.92  #Strategies tried      : 1
% 4.74/1.92  
% 4.74/1.92  Timing (in seconds)
% 4.74/1.92  ----------------------
% 4.74/1.92  Preprocessing        : 0.35
% 4.74/1.92  Parsing              : 0.19
% 4.74/1.92  CNF conversion       : 0.02
% 4.74/1.92  Main loop            : 0.79
% 4.74/1.92  Inferencing          : 0.25
% 4.74/1.92  Reduction            : 0.36
% 4.74/1.92  Demodulation         : 0.29
% 4.74/1.92  BG Simplification    : 0.03
% 4.74/1.92  Subsumption          : 0.10
% 4.74/1.92  Abstraction          : 0.05
% 4.74/1.92  MUC search           : 0.00
% 4.74/1.93  Cooper               : 0.00
% 4.74/1.93  Total                : 1.17
% 4.74/1.93  Index Insertion      : 0.00
% 4.74/1.93  Index Deletion       : 0.00
% 4.74/1.93  Index Matching       : 0.00
% 4.74/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
