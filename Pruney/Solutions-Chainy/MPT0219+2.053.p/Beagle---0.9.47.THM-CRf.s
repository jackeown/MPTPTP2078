%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:56 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 5.13s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 385 expanded)
%              Number of leaves         :   43 ( 148 expanded)
%              Depth                    :   23
%              Number of atoms          :   92 ( 547 expanded)
%              Number of equality atoms :   52 ( 241 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_8 > #skF_9 > #skF_5 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_70,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_68,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_60,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_94,plain,(
    '#skF_10' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_70,plain,(
    ! [C_43] : r2_hidden(C_43,k1_tarski(C_43)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    ! [A_24] : k5_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,(
    ! [A_22,B_23] : r1_tarski(k4_xboole_0(A_22,B_23),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_179,plain,(
    ! [A_94,B_95] :
      ( k3_xboole_0(A_94,B_95) = A_94
      | ~ r1_tarski(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1297,plain,(
    ! [A_179,B_180] : k3_xboole_0(k4_xboole_0(A_179,B_180),A_179) = k4_xboole_0(A_179,B_180) ),
    inference(resolution,[status(thm)],[c_34,c_179])).

tff(c_38,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_4'(A_16),A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_251,plain,(
    ! [A_108,B_109,C_110] :
      ( ~ r1_xboole_0(A_108,B_109)
      | ~ r2_hidden(C_110,k3_xboole_0(A_108,B_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_267,plain,(
    ! [A_113,B_114] :
      ( ~ r1_xboole_0(A_113,B_114)
      | k3_xboole_0(A_113,B_114) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_251])).

tff(c_271,plain,(
    ! [A_25,B_26] : k3_xboole_0(k4_xboole_0(A_25,B_26),B_26) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_267])).

tff(c_1323,plain,(
    ! [A_179] : k4_xboole_0(A_179,A_179) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1297,c_271])).

tff(c_22,plain,(
    ! [A_9] : k3_xboole_0(A_9,A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_326,plain,(
    ! [A_121,B_122] : k5_xboole_0(A_121,k3_xboole_0(A_121,B_122)) = k4_xboole_0(A_121,B_122) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_344,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k4_xboole_0(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_326])).

tff(c_1374,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1323,c_344])).

tff(c_96,plain,(
    k2_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_10')) = k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_42,plain,(
    ! [A_30,B_31] : k5_xboole_0(A_30,k4_xboole_0(B_31,A_30)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_557,plain,(
    ! [A_137,B_138] :
      ( r2_hidden('#skF_3'(A_137,B_138),k3_xboole_0(A_137,B_138))
      | r1_xboole_0(A_137,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_698,plain,(
    ! [A_150,B_151] :
      ( r2_hidden('#skF_3'(A_150,B_151),B_151)
      | r1_xboole_0(A_150,B_151) ) ),
    inference(resolution,[status(thm)],[c_557,c_6])).

tff(c_287,plain,(
    ! [A_118,B_119] : k3_xboole_0(k4_xboole_0(A_118,B_119),B_119) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_267])).

tff(c_26,plain,(
    ! [A_11,B_12,C_15] :
      ( ~ r1_xboole_0(A_11,B_12)
      | ~ r2_hidden(C_15,k3_xboole_0(A_11,B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_295,plain,(
    ! [A_118,B_119,C_15] :
      ( ~ r1_xboole_0(k4_xboole_0(A_118,B_119),B_119)
      | ~ r2_hidden(C_15,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_26])).

tff(c_317,plain,(
    ! [C_15] : ~ r2_hidden(C_15,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_295])).

tff(c_730,plain,(
    ! [A_152] : r1_xboole_0(A_152,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_698,c_317])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_589,plain,(
    ! [A_139,B_140,C_141] :
      ( ~ r1_xboole_0(A_139,B_140)
      | ~ r2_hidden(C_141,k3_xboole_0(B_140,A_139)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_251])).

tff(c_617,plain,(
    ! [A_139,B_140] :
      ( ~ r1_xboole_0(A_139,B_140)
      | k3_xboole_0(B_140,A_139) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_589])).

tff(c_763,plain,(
    ! [A_154] : k3_xboole_0(k1_xboole_0,A_154) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_730,c_617])).

tff(c_338,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_326])).

tff(c_768,plain,(
    ! [A_154] : k5_xboole_0(A_154,k1_xboole_0) = k4_xboole_0(A_154,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_338])).

tff(c_969,plain,(
    ! [A_163] : k4_xboole_0(A_163,k1_xboole_0) = A_163 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_768])).

tff(c_987,plain,(
    ! [A_163] : k5_xboole_0(k1_xboole_0,A_163) = k2_xboole_0(k1_xboole_0,A_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_969,c_42])).

tff(c_1447,plain,(
    ! [A_188] : k5_xboole_0(A_188,A_188) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1323,c_344])).

tff(c_40,plain,(
    ! [A_27,B_28,C_29] : k5_xboole_0(k5_xboole_0(A_27,B_28),C_29) = k5_xboole_0(A_27,k5_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1460,plain,(
    ! [A_188,C_29] : k5_xboole_0(A_188,k5_xboole_0(A_188,C_29)) = k5_xboole_0(k1_xboole_0,C_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_1447,c_40])).

tff(c_2839,plain,(
    ! [A_274,C_275] : k5_xboole_0(A_274,k5_xboole_0(A_274,C_275)) = k2_xboole_0(k1_xboole_0,C_275) ),
    inference(demodulation,[status(thm),theory(equality)],[c_987,c_1460])).

tff(c_2886,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_1374,c_2839])).

tff(c_2928,plain,(
    ! [A_9] : k2_xboole_0(k1_xboole_0,A_9) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2886])).

tff(c_1489,plain,(
    ! [A_188,C_29] : k5_xboole_0(A_188,k5_xboole_0(A_188,C_29)) = k2_xboole_0(k1_xboole_0,C_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_987,c_1460])).

tff(c_3091,plain,(
    ! [A_281,C_282] : k5_xboole_0(A_281,k5_xboole_0(A_281,C_282)) = C_282 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2928,c_1489])).

tff(c_3637,plain,(
    ! [A_309,B_310] : k5_xboole_0(A_309,k2_xboole_0(A_309,B_310)) = k4_xboole_0(B_310,A_309) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_3091])).

tff(c_3692,plain,(
    k5_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_9')) = k4_xboole_0(k1_tarski('#skF_10'),k1_tarski('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_3637])).

tff(c_3703,plain,(
    k4_xboole_0(k1_tarski('#skF_10'),k1_tarski('#skF_9')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1374,c_3692])).

tff(c_30,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3890,plain,(
    ! [A_313,B_314] : k5_xboole_0(A_313,k4_xboole_0(A_313,B_314)) = k3_xboole_0(A_313,B_314) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3091])).

tff(c_3932,plain,(
    k3_xboole_0(k1_tarski('#skF_10'),k1_tarski('#skF_9')) = k5_xboole_0(k1_tarski('#skF_10'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3703,c_3890])).

tff(c_3968,plain,(
    k3_xboole_0(k1_tarski('#skF_10'),k1_tarski('#skF_9')) = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3932])).

tff(c_4470,plain,(
    ! [D_327] :
      ( r2_hidden(D_327,k1_tarski('#skF_9'))
      | ~ r2_hidden(D_327,k1_tarski('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3968,c_6])).

tff(c_4540,plain,(
    r2_hidden('#skF_10',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_70,c_4470])).

tff(c_68,plain,(
    ! [C_43,A_39] :
      ( C_43 = A_39
      | ~ r2_hidden(C_43,k1_tarski(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4543,plain,(
    '#skF_10' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_4540,c_68])).

tff(c_4547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_4543])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:54:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.74/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.92  
% 4.74/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.92  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_8 > #skF_9 > #skF_5 > #skF_7
% 4.74/1.92  
% 4.74/1.92  %Foreground sorts:
% 4.74/1.92  
% 4.74/1.92  
% 4.74/1.92  %Background operators:
% 4.74/1.92  
% 4.74/1.92  
% 4.74/1.92  %Foreground operators:
% 4.74/1.92  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.74/1.92  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.74/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.74/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.74/1.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.74/1.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.74/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.74/1.92  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.74/1.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.74/1.92  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.74/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.74/1.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.74/1.92  tff('#skF_10', type, '#skF_10': $i).
% 4.74/1.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.74/1.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.74/1.92  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.74/1.92  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.74/1.92  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 4.74/1.92  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 4.74/1.92  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.74/1.92  tff('#skF_9', type, '#skF_9': $i).
% 4.74/1.92  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.74/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.74/1.92  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 4.74/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.74/1.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.74/1.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.74/1.92  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.74/1.92  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.74/1.92  
% 5.13/1.94  tff(f_117, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 5.13/1.94  tff(f_98, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 5.13/1.94  tff(f_70, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.13/1.94  tff(f_68, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.13/1.94  tff(f_66, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.13/1.94  tff(f_72, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.13/1.94  tff(f_60, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.13/1.94  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.13/1.94  tff(f_38, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.13/1.94  tff(f_62, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.13/1.94  tff(f_76, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.13/1.94  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.13/1.94  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.13/1.94  tff(f_74, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.13/1.94  tff(c_94, plain, ('#skF_10'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.13/1.94  tff(c_70, plain, (![C_43]: (r2_hidden(C_43, k1_tarski(C_43)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.13/1.94  tff(c_36, plain, (![A_24]: (k5_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.13/1.94  tff(c_34, plain, (![A_22, B_23]: (r1_tarski(k4_xboole_0(A_22, B_23), A_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.13/1.94  tff(c_179, plain, (![A_94, B_95]: (k3_xboole_0(A_94, B_95)=A_94 | ~r1_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.13/1.94  tff(c_1297, plain, (![A_179, B_180]: (k3_xboole_0(k4_xboole_0(A_179, B_180), A_179)=k4_xboole_0(A_179, B_180))), inference(resolution, [status(thm)], [c_34, c_179])).
% 5.13/1.94  tff(c_38, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.13/1.94  tff(c_28, plain, (![A_16]: (r2_hidden('#skF_4'(A_16), A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.13/1.94  tff(c_251, plain, (![A_108, B_109, C_110]: (~r1_xboole_0(A_108, B_109) | ~r2_hidden(C_110, k3_xboole_0(A_108, B_109)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.13/1.94  tff(c_267, plain, (![A_113, B_114]: (~r1_xboole_0(A_113, B_114) | k3_xboole_0(A_113, B_114)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_251])).
% 5.13/1.94  tff(c_271, plain, (![A_25, B_26]: (k3_xboole_0(k4_xboole_0(A_25, B_26), B_26)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_267])).
% 5.13/1.94  tff(c_1323, plain, (![A_179]: (k4_xboole_0(A_179, A_179)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1297, c_271])).
% 5.13/1.94  tff(c_22, plain, (![A_9]: (k3_xboole_0(A_9, A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.13/1.94  tff(c_326, plain, (![A_121, B_122]: (k5_xboole_0(A_121, k3_xboole_0(A_121, B_122))=k4_xboole_0(A_121, B_122))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.13/1.94  tff(c_344, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k4_xboole_0(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_22, c_326])).
% 5.13/1.94  tff(c_1374, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1323, c_344])).
% 5.13/1.94  tff(c_96, plain, (k2_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_10'))=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.13/1.94  tff(c_42, plain, (![A_30, B_31]: (k5_xboole_0(A_30, k4_xboole_0(B_31, A_30))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.13/1.94  tff(c_557, plain, (![A_137, B_138]: (r2_hidden('#skF_3'(A_137, B_138), k3_xboole_0(A_137, B_138)) | r1_xboole_0(A_137, B_138))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.13/1.94  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.13/1.94  tff(c_698, plain, (![A_150, B_151]: (r2_hidden('#skF_3'(A_150, B_151), B_151) | r1_xboole_0(A_150, B_151))), inference(resolution, [status(thm)], [c_557, c_6])).
% 5.13/1.94  tff(c_287, plain, (![A_118, B_119]: (k3_xboole_0(k4_xboole_0(A_118, B_119), B_119)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_267])).
% 5.13/1.94  tff(c_26, plain, (![A_11, B_12, C_15]: (~r1_xboole_0(A_11, B_12) | ~r2_hidden(C_15, k3_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.13/1.94  tff(c_295, plain, (![A_118, B_119, C_15]: (~r1_xboole_0(k4_xboole_0(A_118, B_119), B_119) | ~r2_hidden(C_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_287, c_26])).
% 5.13/1.94  tff(c_317, plain, (![C_15]: (~r2_hidden(C_15, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_295])).
% 5.13/1.94  tff(c_730, plain, (![A_152]: (r1_xboole_0(A_152, k1_xboole_0))), inference(resolution, [status(thm)], [c_698, c_317])).
% 5.13/1.94  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.13/1.94  tff(c_589, plain, (![A_139, B_140, C_141]: (~r1_xboole_0(A_139, B_140) | ~r2_hidden(C_141, k3_xboole_0(B_140, A_139)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_251])).
% 5.13/1.94  tff(c_617, plain, (![A_139, B_140]: (~r1_xboole_0(A_139, B_140) | k3_xboole_0(B_140, A_139)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_589])).
% 5.13/1.94  tff(c_763, plain, (![A_154]: (k3_xboole_0(k1_xboole_0, A_154)=k1_xboole_0)), inference(resolution, [status(thm)], [c_730, c_617])).
% 5.13/1.94  tff(c_338, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_326])).
% 5.13/1.94  tff(c_768, plain, (![A_154]: (k5_xboole_0(A_154, k1_xboole_0)=k4_xboole_0(A_154, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_763, c_338])).
% 5.13/1.94  tff(c_969, plain, (![A_163]: (k4_xboole_0(A_163, k1_xboole_0)=A_163)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_768])).
% 5.13/1.94  tff(c_987, plain, (![A_163]: (k5_xboole_0(k1_xboole_0, A_163)=k2_xboole_0(k1_xboole_0, A_163))), inference(superposition, [status(thm), theory('equality')], [c_969, c_42])).
% 5.13/1.94  tff(c_1447, plain, (![A_188]: (k5_xboole_0(A_188, A_188)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1323, c_344])).
% 5.13/1.94  tff(c_40, plain, (![A_27, B_28, C_29]: (k5_xboole_0(k5_xboole_0(A_27, B_28), C_29)=k5_xboole_0(A_27, k5_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.13/1.94  tff(c_1460, plain, (![A_188, C_29]: (k5_xboole_0(A_188, k5_xboole_0(A_188, C_29))=k5_xboole_0(k1_xboole_0, C_29))), inference(superposition, [status(thm), theory('equality')], [c_1447, c_40])).
% 5.13/1.94  tff(c_2839, plain, (![A_274, C_275]: (k5_xboole_0(A_274, k5_xboole_0(A_274, C_275))=k2_xboole_0(k1_xboole_0, C_275))), inference(demodulation, [status(thm), theory('equality')], [c_987, c_1460])).
% 5.13/1.94  tff(c_2886, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_9))), inference(superposition, [status(thm), theory('equality')], [c_1374, c_2839])).
% 5.13/1.94  tff(c_2928, plain, (![A_9]: (k2_xboole_0(k1_xboole_0, A_9)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2886])).
% 5.13/1.94  tff(c_1489, plain, (![A_188, C_29]: (k5_xboole_0(A_188, k5_xboole_0(A_188, C_29))=k2_xboole_0(k1_xboole_0, C_29))), inference(demodulation, [status(thm), theory('equality')], [c_987, c_1460])).
% 5.13/1.94  tff(c_3091, plain, (![A_281, C_282]: (k5_xboole_0(A_281, k5_xboole_0(A_281, C_282))=C_282)), inference(demodulation, [status(thm), theory('equality')], [c_2928, c_1489])).
% 5.13/1.94  tff(c_3637, plain, (![A_309, B_310]: (k5_xboole_0(A_309, k2_xboole_0(A_309, B_310))=k4_xboole_0(B_310, A_309))), inference(superposition, [status(thm), theory('equality')], [c_42, c_3091])).
% 5.13/1.94  tff(c_3692, plain, (k5_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_9'))=k4_xboole_0(k1_tarski('#skF_10'), k1_tarski('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_3637])).
% 5.13/1.94  tff(c_3703, plain, (k4_xboole_0(k1_tarski('#skF_10'), k1_tarski('#skF_9'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1374, c_3692])).
% 5.13/1.94  tff(c_30, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.13/1.94  tff(c_3890, plain, (![A_313, B_314]: (k5_xboole_0(A_313, k4_xboole_0(A_313, B_314))=k3_xboole_0(A_313, B_314))), inference(superposition, [status(thm), theory('equality')], [c_30, c_3091])).
% 5.13/1.94  tff(c_3932, plain, (k3_xboole_0(k1_tarski('#skF_10'), k1_tarski('#skF_9'))=k5_xboole_0(k1_tarski('#skF_10'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3703, c_3890])).
% 5.13/1.94  tff(c_3968, plain, (k3_xboole_0(k1_tarski('#skF_10'), k1_tarski('#skF_9'))=k1_tarski('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3932])).
% 5.13/1.94  tff(c_4470, plain, (![D_327]: (r2_hidden(D_327, k1_tarski('#skF_9')) | ~r2_hidden(D_327, k1_tarski('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_3968, c_6])).
% 5.13/1.94  tff(c_4540, plain, (r2_hidden('#skF_10', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_70, c_4470])).
% 5.13/1.94  tff(c_68, plain, (![C_43, A_39]: (C_43=A_39 | ~r2_hidden(C_43, k1_tarski(A_39)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.13/1.94  tff(c_4543, plain, ('#skF_10'='#skF_9'), inference(resolution, [status(thm)], [c_4540, c_68])).
% 5.13/1.94  tff(c_4547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_4543])).
% 5.13/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.13/1.94  
% 5.13/1.94  Inference rules
% 5.13/1.94  ----------------------
% 5.13/1.94  #Ref     : 0
% 5.13/1.94  #Sup     : 1052
% 5.13/1.94  #Fact    : 0
% 5.13/1.94  #Define  : 0
% 5.13/1.94  #Split   : 0
% 5.13/1.94  #Chain   : 0
% 5.13/1.94  #Close   : 0
% 5.13/1.94  
% 5.13/1.94  Ordering : KBO
% 5.13/1.94  
% 5.13/1.94  Simplification rules
% 5.13/1.94  ----------------------
% 5.13/1.94  #Subsume      : 99
% 5.13/1.94  #Demod        : 678
% 5.13/1.94  #Tautology    : 612
% 5.13/1.94  #SimpNegUnit  : 15
% 5.13/1.94  #BackRed      : 5
% 5.13/1.94  
% 5.13/1.94  #Partial instantiations: 0
% 5.13/1.94  #Strategies tried      : 1
% 5.13/1.94  
% 5.13/1.94  Timing (in seconds)
% 5.13/1.94  ----------------------
% 5.13/1.94  Preprocessing        : 0.36
% 5.13/1.94  Parsing              : 0.18
% 5.13/1.94  CNF conversion       : 0.03
% 5.13/1.94  Main loop            : 0.81
% 5.13/1.94  Inferencing          : 0.27
% 5.13/1.94  Reduction            : 0.31
% 5.13/1.94  Demodulation         : 0.24
% 5.13/1.94  BG Simplification    : 0.04
% 5.13/1.94  Subsumption          : 0.14
% 5.13/1.94  Abstraction          : 0.04
% 5.13/1.94  MUC search           : 0.00
% 5.13/1.94  Cooper               : 0.00
% 5.13/1.94  Total                : 1.21
% 5.13/1.94  Index Insertion      : 0.00
% 5.13/1.94  Index Deletion       : 0.00
% 5.13/1.94  Index Matching       : 0.00
% 5.13/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
