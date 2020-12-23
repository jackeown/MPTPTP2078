%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:18 EST 2020

% Result     : Theorem 7.90s
% Output     : CNFRefutation 8.15s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 372 expanded)
%              Number of leaves         :   31 ( 139 expanded)
%              Depth                    :   15
%              Number of atoms          :   78 ( 434 expanded)
%              Number of equality atoms :   53 ( 329 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(c_48,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_572,plain,(
    ! [A_100,B_101,C_102] :
      ( r1_tarski(k2_tarski(A_100,B_101),C_102)
      | ~ r2_hidden(B_101,C_102)
      | ~ r2_hidden(A_100,C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2626,plain,(
    ! [A_163,B_164,C_165] :
      ( k4_xboole_0(k2_tarski(A_163,B_164),C_165) = k1_xboole_0
      | ~ r2_hidden(B_164,C_165)
      | ~ r2_hidden(A_163,C_165) ) ),
    inference(resolution,[status(thm)],[c_572,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_137,plain,(
    ! [A_63,B_64] : k5_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_146,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_137])).

tff(c_355,plain,(
    ! [A_94,B_95,C_96] : k5_xboole_0(k5_xboole_0(A_94,B_95),C_96) = k5_xboole_0(A_94,k5_xboole_0(B_95,C_96)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_15,B_16] : k5_xboole_0(k5_xboole_0(A_15,B_16),k3_xboole_0(A_15,B_16)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_368,plain,(
    ! [A_94,B_95] : k5_xboole_0(A_94,k5_xboole_0(B_95,k3_xboole_0(A_94,B_95))) = k2_xboole_0(A_94,B_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_22])).

tff(c_430,plain,(
    ! [A_94,B_95] : k5_xboole_0(A_94,k4_xboole_0(B_95,A_94)) = k2_xboole_0(A_94,B_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_368])).

tff(c_2646,plain,(
    ! [C_165,A_163,B_164] :
      ( k2_xboole_0(C_165,k2_tarski(A_163,B_164)) = k5_xboole_0(C_165,k1_xboole_0)
      | ~ r2_hidden(B_164,C_165)
      | ~ r2_hidden(A_163,C_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2626,c_430])).

tff(c_2676,plain,(
    ! [C_165,A_163,B_164] :
      ( k2_xboole_0(C_165,k2_tarski(A_163,B_164)) = C_165
      | ~ r2_hidden(B_164,C_165)
      | ~ r2_hidden(A_163,C_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2646])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_111,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = k1_xboole_0
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_115,plain,(
    ! [B_6] : k4_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_111])).

tff(c_635,plain,(
    ! [A_104,B_105] : k5_xboole_0(A_104,k4_xboole_0(B_105,A_104)) = k2_xboole_0(A_104,B_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_368])).

tff(c_666,plain,(
    ! [B_6] : k5_xboole_0(B_6,k1_xboole_0) = k2_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_635])).

tff(c_669,plain,(
    ! [B_6] : k2_xboole_0(B_6,B_6) = B_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_666])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_152,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_137])).

tff(c_155,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_152])).

tff(c_274,plain,(
    ! [A_91,B_92] : k5_xboole_0(k5_xboole_0(A_91,B_92),k3_xboole_0(A_91,B_92)) = k2_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_304,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k2_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_274])).

tff(c_313,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = k2_xboole_0(A_3,A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_304])).

tff(c_681,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_313])).

tff(c_409,plain,(
    ! [A_3,C_96] : k5_xboole_0(A_3,k5_xboole_0(A_3,C_96)) = k5_xboole_0(k1_xboole_0,C_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_355])).

tff(c_1107,plain,(
    ! [A_137,C_138] : k5_xboole_0(A_137,k5_xboole_0(A_137,C_138)) = C_138 ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_409])).

tff(c_2536,plain,(
    ! [A_161,B_162] : k5_xboole_0(A_161,k2_xboole_0(A_161,B_162)) = k4_xboole_0(B_162,A_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_1107])).

tff(c_1185,plain,(
    ! [A_139,B_140] : k5_xboole_0(A_139,k5_xboole_0(B_140,k5_xboole_0(A_139,B_140))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_355])).

tff(c_1106,plain,(
    ! [A_3,C_96] : k5_xboole_0(A_3,k5_xboole_0(A_3,C_96)) = C_96 ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_409])).

tff(c_1193,plain,(
    ! [B_140,A_139] : k5_xboole_0(B_140,k5_xboole_0(A_139,B_140)) = k5_xboole_0(A_139,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1185,c_1106])).

tff(c_1294,plain,(
    ! [B_141,A_142] : k5_xboole_0(B_141,k5_xboole_0(A_142,B_141)) = A_142 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1193])).

tff(c_1276,plain,(
    ! [B_140,A_139] : k5_xboole_0(B_140,k5_xboole_0(A_139,B_140)) = A_139 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1193])).

tff(c_1297,plain,(
    ! [A_142,B_141] : k5_xboole_0(k5_xboole_0(A_142,B_141),A_142) = B_141 ),
    inference(superposition,[status(thm),theory(equality)],[c_1294,c_1276])).

tff(c_2560,plain,(
    ! [B_162,A_161] : k5_xboole_0(k4_xboole_0(B_162,A_161),A_161) = k2_xboole_0(A_161,B_162) ),
    inference(superposition,[status(thm),theory(equality)],[c_2536,c_1297])).

tff(c_16,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3180,plain,(
    ! [A_178,B_179,C_180] : k5_xboole_0(A_178,k5_xboole_0(k3_xboole_0(A_178,B_179),C_180)) = k5_xboole_0(k4_xboole_0(A_178,B_179),C_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_355])).

tff(c_3312,plain,(
    ! [A_178,B_179] : k5_xboole_0(k4_xboole_0(A_178,B_179),k3_xboole_0(A_178,B_179)) = k5_xboole_0(A_178,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_3180])).

tff(c_3346,plain,(
    ! [A_181,B_182] : k5_xboole_0(k4_xboole_0(A_181,B_182),k3_xboole_0(A_181,B_182)) = A_181 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3312])).

tff(c_3371,plain,(
    ! [A_181,B_182] : k5_xboole_0(k3_xboole_0(A_181,B_182),A_181) = k4_xboole_0(A_181,B_182) ),
    inference(superposition,[status(thm),theory(equality)],[c_3346,c_1276])).

tff(c_9820,plain,(
    ! [A_246,B_247,C_248] : k5_xboole_0(A_246,k5_xboole_0(k3_xboole_0(B_247,A_246),C_248)) = k5_xboole_0(k4_xboole_0(A_246,B_247),C_248) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3180])).

tff(c_9957,plain,(
    ! [B_182,A_181] : k5_xboole_0(k4_xboole_0(B_182,A_181),A_181) = k5_xboole_0(B_182,k4_xboole_0(A_181,B_182)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3371,c_9820])).

tff(c_10101,plain,(
    ! [B_182,A_181] : k2_xboole_0(B_182,A_181) = k2_xboole_0(A_181,B_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2560,c_430,c_9957])).

tff(c_44,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10119,plain,(
    k2_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10101,c_44])).

tff(c_10439,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2676,c_10119])).

tff(c_10443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_10439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:08:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.90/3.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.90/3.10  
% 7.90/3.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.90/3.11  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.90/3.11  
% 7.90/3.11  %Foreground sorts:
% 7.90/3.11  
% 7.90/3.11  
% 7.90/3.11  %Background operators:
% 7.90/3.11  
% 7.90/3.11  
% 7.90/3.11  %Foreground operators:
% 7.90/3.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.90/3.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.90/3.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.90/3.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.90/3.11  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.90/3.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.90/3.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.90/3.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.90/3.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.90/3.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.90/3.11  tff('#skF_2', type, '#skF_2': $i).
% 7.90/3.11  tff('#skF_3', type, '#skF_3': $i).
% 7.90/3.11  tff('#skF_1', type, '#skF_1': $i).
% 7.90/3.11  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.90/3.11  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.90/3.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.90/3.11  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.90/3.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.90/3.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.90/3.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.90/3.11  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.90/3.11  
% 8.15/3.12  tff(f_74, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 8.15/3.12  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 8.15/3.12  tff(f_67, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 8.15/3.12  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.15/3.12  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.15/3.12  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.15/3.12  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.15/3.12  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 8.15/3.12  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.15/3.12  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.15/3.12  tff(c_48, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.15/3.12  tff(c_46, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.15/3.12  tff(c_18, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.15/3.12  tff(c_572, plain, (![A_100, B_101, C_102]: (r1_tarski(k2_tarski(A_100, B_101), C_102) | ~r2_hidden(B_101, C_102) | ~r2_hidden(A_100, C_102))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.15/3.12  tff(c_14, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.15/3.12  tff(c_2626, plain, (![A_163, B_164, C_165]: (k4_xboole_0(k2_tarski(A_163, B_164), C_165)=k1_xboole_0 | ~r2_hidden(B_164, C_165) | ~r2_hidden(A_163, C_165))), inference(resolution, [status(thm)], [c_572, c_14])).
% 8.15/3.12  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.15/3.12  tff(c_137, plain, (![A_63, B_64]: (k5_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.15/3.12  tff(c_146, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_137])).
% 8.15/3.12  tff(c_355, plain, (![A_94, B_95, C_96]: (k5_xboole_0(k5_xboole_0(A_94, B_95), C_96)=k5_xboole_0(A_94, k5_xboole_0(B_95, C_96)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.15/3.12  tff(c_22, plain, (![A_15, B_16]: (k5_xboole_0(k5_xboole_0(A_15, B_16), k3_xboole_0(A_15, B_16))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.15/3.12  tff(c_368, plain, (![A_94, B_95]: (k5_xboole_0(A_94, k5_xboole_0(B_95, k3_xboole_0(A_94, B_95)))=k2_xboole_0(A_94, B_95))), inference(superposition, [status(thm), theory('equality')], [c_355, c_22])).
% 8.15/3.12  tff(c_430, plain, (![A_94, B_95]: (k5_xboole_0(A_94, k4_xboole_0(B_95, A_94))=k2_xboole_0(A_94, B_95))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_368])).
% 8.15/3.12  tff(c_2646, plain, (![C_165, A_163, B_164]: (k2_xboole_0(C_165, k2_tarski(A_163, B_164))=k5_xboole_0(C_165, k1_xboole_0) | ~r2_hidden(B_164, C_165) | ~r2_hidden(A_163, C_165))), inference(superposition, [status(thm), theory('equality')], [c_2626, c_430])).
% 8.15/3.12  tff(c_2676, plain, (![C_165, A_163, B_164]: (k2_xboole_0(C_165, k2_tarski(A_163, B_164))=C_165 | ~r2_hidden(B_164, C_165) | ~r2_hidden(A_163, C_165))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2646])).
% 8.15/3.12  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.15/3.12  tff(c_111, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=k1_xboole_0 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.15/3.12  tff(c_115, plain, (![B_6]: (k4_xboole_0(B_6, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_111])).
% 8.15/3.12  tff(c_635, plain, (![A_104, B_105]: (k5_xboole_0(A_104, k4_xboole_0(B_105, A_104))=k2_xboole_0(A_104, B_105))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_368])).
% 8.15/3.12  tff(c_666, plain, (![B_6]: (k5_xboole_0(B_6, k1_xboole_0)=k2_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_115, c_635])).
% 8.15/3.12  tff(c_669, plain, (![B_6]: (k2_xboole_0(B_6, B_6)=B_6)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_666])).
% 8.15/3.12  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.15/3.12  tff(c_152, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_137])).
% 8.15/3.12  tff(c_155, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_115, c_152])).
% 8.15/3.12  tff(c_274, plain, (![A_91, B_92]: (k5_xboole_0(k5_xboole_0(A_91, B_92), k3_xboole_0(A_91, B_92))=k2_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.15/3.12  tff(c_304, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k2_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_274])).
% 8.15/3.12  tff(c_313, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=k2_xboole_0(A_3, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_304])).
% 8.15/3.12  tff(c_681, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_669, c_313])).
% 8.15/3.12  tff(c_409, plain, (![A_3, C_96]: (k5_xboole_0(A_3, k5_xboole_0(A_3, C_96))=k5_xboole_0(k1_xboole_0, C_96))), inference(superposition, [status(thm), theory('equality')], [c_155, c_355])).
% 8.15/3.12  tff(c_1107, plain, (![A_137, C_138]: (k5_xboole_0(A_137, k5_xboole_0(A_137, C_138))=C_138)), inference(demodulation, [status(thm), theory('equality')], [c_681, c_409])).
% 8.15/3.12  tff(c_2536, plain, (![A_161, B_162]: (k5_xboole_0(A_161, k2_xboole_0(A_161, B_162))=k4_xboole_0(B_162, A_161))), inference(superposition, [status(thm), theory('equality')], [c_430, c_1107])).
% 8.15/3.12  tff(c_1185, plain, (![A_139, B_140]: (k5_xboole_0(A_139, k5_xboole_0(B_140, k5_xboole_0(A_139, B_140)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_155, c_355])).
% 8.15/3.12  tff(c_1106, plain, (![A_3, C_96]: (k5_xboole_0(A_3, k5_xboole_0(A_3, C_96))=C_96)), inference(demodulation, [status(thm), theory('equality')], [c_681, c_409])).
% 8.15/3.12  tff(c_1193, plain, (![B_140, A_139]: (k5_xboole_0(B_140, k5_xboole_0(A_139, B_140))=k5_xboole_0(A_139, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1185, c_1106])).
% 8.15/3.12  tff(c_1294, plain, (![B_141, A_142]: (k5_xboole_0(B_141, k5_xboole_0(A_142, B_141))=A_142)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1193])).
% 8.15/3.12  tff(c_1276, plain, (![B_140, A_139]: (k5_xboole_0(B_140, k5_xboole_0(A_139, B_140))=A_139)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1193])).
% 8.15/3.12  tff(c_1297, plain, (![A_142, B_141]: (k5_xboole_0(k5_xboole_0(A_142, B_141), A_142)=B_141)), inference(superposition, [status(thm), theory('equality')], [c_1294, c_1276])).
% 8.15/3.12  tff(c_2560, plain, (![B_162, A_161]: (k5_xboole_0(k4_xboole_0(B_162, A_161), A_161)=k2_xboole_0(A_161, B_162))), inference(superposition, [status(thm), theory('equality')], [c_2536, c_1297])).
% 8.15/3.12  tff(c_16, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.15/3.12  tff(c_3180, plain, (![A_178, B_179, C_180]: (k5_xboole_0(A_178, k5_xboole_0(k3_xboole_0(A_178, B_179), C_180))=k5_xboole_0(k4_xboole_0(A_178, B_179), C_180))), inference(superposition, [status(thm), theory('equality')], [c_16, c_355])).
% 8.15/3.12  tff(c_3312, plain, (![A_178, B_179]: (k5_xboole_0(k4_xboole_0(A_178, B_179), k3_xboole_0(A_178, B_179))=k5_xboole_0(A_178, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_155, c_3180])).
% 8.15/3.12  tff(c_3346, plain, (![A_181, B_182]: (k5_xboole_0(k4_xboole_0(A_181, B_182), k3_xboole_0(A_181, B_182))=A_181)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3312])).
% 8.15/3.12  tff(c_3371, plain, (![A_181, B_182]: (k5_xboole_0(k3_xboole_0(A_181, B_182), A_181)=k4_xboole_0(A_181, B_182))), inference(superposition, [status(thm), theory('equality')], [c_3346, c_1276])).
% 8.15/3.12  tff(c_9820, plain, (![A_246, B_247, C_248]: (k5_xboole_0(A_246, k5_xboole_0(k3_xboole_0(B_247, A_246), C_248))=k5_xboole_0(k4_xboole_0(A_246, B_247), C_248))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3180])).
% 8.15/3.12  tff(c_9957, plain, (![B_182, A_181]: (k5_xboole_0(k4_xboole_0(B_182, A_181), A_181)=k5_xboole_0(B_182, k4_xboole_0(A_181, B_182)))), inference(superposition, [status(thm), theory('equality')], [c_3371, c_9820])).
% 8.15/3.12  tff(c_10101, plain, (![B_182, A_181]: (k2_xboole_0(B_182, A_181)=k2_xboole_0(A_181, B_182))), inference(demodulation, [status(thm), theory('equality')], [c_2560, c_430, c_9957])).
% 8.15/3.12  tff(c_44, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.15/3.12  tff(c_10119, plain, (k2_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10101, c_44])).
% 8.15/3.12  tff(c_10439, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2676, c_10119])).
% 8.15/3.12  tff(c_10443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_10439])).
% 8.15/3.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.15/3.12  
% 8.15/3.12  Inference rules
% 8.15/3.12  ----------------------
% 8.15/3.12  #Ref     : 0
% 8.15/3.12  #Sup     : 2498
% 8.15/3.12  #Fact    : 0
% 8.15/3.12  #Define  : 0
% 8.15/3.12  #Split   : 0
% 8.15/3.12  #Chain   : 0
% 8.15/3.12  #Close   : 0
% 8.15/3.12  
% 8.15/3.12  Ordering : KBO
% 8.15/3.12  
% 8.15/3.12  Simplification rules
% 8.15/3.12  ----------------------
% 8.15/3.12  #Subsume      : 66
% 8.15/3.12  #Demod        : 2782
% 8.15/3.12  #Tautology    : 1366
% 8.15/3.12  #SimpNegUnit  : 0
% 8.15/3.12  #BackRed      : 6
% 8.15/3.12  
% 8.15/3.12  #Partial instantiations: 0
% 8.15/3.12  #Strategies tried      : 1
% 8.15/3.12  
% 8.15/3.12  Timing (in seconds)
% 8.15/3.12  ----------------------
% 8.15/3.13  Preprocessing        : 0.33
% 8.15/3.13  Parsing              : 0.18
% 8.15/3.13  CNF conversion       : 0.02
% 8.15/3.13  Main loop            : 1.97
% 8.15/3.13  Inferencing          : 0.48
% 8.15/3.13  Reduction            : 1.06
% 8.15/3.13  Demodulation         : 0.94
% 8.15/3.13  BG Simplification    : 0.07
% 8.15/3.13  Subsumption          : 0.26
% 8.15/3.13  Abstraction          : 0.10
% 8.15/3.13  MUC search           : 0.00
% 8.15/3.13  Cooper               : 0.00
% 8.15/3.13  Total                : 2.33
% 8.15/3.13  Index Insertion      : 0.00
% 8.15/3.13  Index Deletion       : 0.00
% 8.15/3.13  Index Matching       : 0.00
% 8.15/3.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
