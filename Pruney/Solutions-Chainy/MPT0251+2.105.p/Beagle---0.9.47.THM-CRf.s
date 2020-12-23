%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:00 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 246 expanded)
%              Number of leaves         :   35 (  99 expanded)
%              Depth                    :   21
%              Number of atoms          :   71 ( 272 expanded)
%              Number of equality atoms :   51 ( 196 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_44,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_510,plain,(
    ! [B_96,A_97] :
      ( k3_xboole_0(B_96,k1_tarski(A_97)) = k1_tarski(A_97)
      | ~ r2_hidden(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_548,plain,(
    ! [A_97,B_2] :
      ( k3_xboole_0(k1_tarski(A_97),B_2) = k1_tarski(A_97)
      | ~ r2_hidden(A_97,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_510])).

tff(c_268,plain,(
    ! [A_78,B_79] : k5_xboole_0(A_78,k3_xboole_0(A_78,B_79)) = k4_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_280,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_268])).

tff(c_12,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_85,plain,(
    ! [A_61,B_62] : k4_xboole_0(A_61,k2_xboole_0(A_61,B_62)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_92,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_85])).

tff(c_191,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k4_xboole_0(B_74,A_73)) = k2_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_203,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = k2_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_191])).

tff(c_18,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_351,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,k3_xboole_0(A_83,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_396,plain,(
    ! [A_92,B_93] :
      ( ~ r1_xboole_0(A_92,B_93)
      | k3_xboole_0(A_92,B_93) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_351])).

tff(c_401,plain,(
    ! [A_94] : k3_xboole_0(A_94,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_396])).

tff(c_440,plain,(
    ! [A_95] : k3_xboole_0(k1_xboole_0,A_95) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_2])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_455,plain,(
    ! [A_95] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_10])).

tff(c_602,plain,(
    ! [A_101] : k4_xboole_0(k1_xboole_0,A_101) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_203,c_455])).

tff(c_610,plain,(
    ! [A_101] : k5_xboole_0(A_101,k1_xboole_0) = k2_xboole_0(A_101,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_22])).

tff(c_630,plain,(
    ! [A_101] : k5_xboole_0(A_101,k1_xboole_0) = A_101 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_610])).

tff(c_16,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_286,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k5_xboole_0(A_13,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_268])).

tff(c_290,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_286])).

tff(c_699,plain,(
    ! [A_105,B_106,C_107] : k5_xboole_0(k5_xboole_0(A_105,B_106),C_107) = k5_xboole_0(A_105,k5_xboole_0(B_106,C_107)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_741,plain,(
    ! [A_105,B_106] : k5_xboole_0(A_105,k5_xboole_0(B_106,k5_xboole_0(A_105,B_106))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_699])).

tff(c_409,plain,(
    ! [A_94] : k5_xboole_0(A_94,k1_xboole_0) = k4_xboole_0(A_94,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_10])).

tff(c_764,plain,(
    ! [A_108] : k4_xboole_0(A_108,k1_xboole_0) = A_108 ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_409])).

tff(c_774,plain,(
    ! [A_108] : k5_xboole_0(k1_xboole_0,A_108) = k2_xboole_0(k1_xboole_0,A_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_764,c_22])).

tff(c_737,plain,(
    ! [A_13,C_107] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_107)) = k5_xboole_0(k1_xboole_0,C_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_699])).

tff(c_1133,plain,(
    ! [A_143,C_144] : k5_xboole_0(A_143,k5_xboole_0(A_143,C_144)) = k2_xboole_0(k1_xboole_0,C_144) ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_737])).

tff(c_1200,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_1133])).

tff(c_1221,plain,(
    ! [A_13] : k2_xboole_0(k1_xboole_0,A_13) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_1200])).

tff(c_1132,plain,(
    ! [A_13,C_107] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_107)) = k2_xboole_0(k1_xboole_0,C_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_737])).

tff(c_1362,plain,(
    ! [A_154,C_155] : k5_xboole_0(A_154,k5_xboole_0(A_154,C_155)) = C_155 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1221,c_1132])).

tff(c_1406,plain,(
    ! [B_106,A_105] : k5_xboole_0(B_106,k5_xboole_0(A_105,B_106)) = k5_xboole_0(A_105,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_741,c_1362])).

tff(c_1470,plain,(
    ! [B_157,A_158] : k5_xboole_0(B_157,k5_xboole_0(A_158,B_157)) = A_158 ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_1406])).

tff(c_2748,plain,(
    ! [A_189,B_190] : k5_xboole_0(k3_xboole_0(A_189,B_190),k4_xboole_0(B_190,A_189)) = B_190 ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_1470])).

tff(c_2786,plain,(
    ! [A_97,B_2] :
      ( k5_xboole_0(k1_tarski(A_97),k4_xboole_0(B_2,k1_tarski(A_97))) = B_2
      | ~ r2_hidden(A_97,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_2748])).

tff(c_2840,plain,(
    ! [A_191,B_192] :
      ( k2_xboole_0(k1_tarski(A_191),B_192) = B_192
      | ~ r2_hidden(A_191,B_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2786])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2876,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2840,c_42])).

tff(c_2903,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2876])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:48:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.80  
% 3.52/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.80  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.52/1.80  
% 3.52/1.80  %Foreground sorts:
% 3.52/1.80  
% 3.52/1.80  
% 3.52/1.80  %Background operators:
% 3.52/1.80  
% 3.52/1.80  
% 3.52/1.80  %Foreground operators:
% 3.52/1.80  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.52/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.52/1.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.52/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.52/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.80  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.52/1.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.52/1.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.52/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.52/1.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.52/1.80  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.52/1.80  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.80  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.80  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.80  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.52/1.80  tff('#skF_4', type, '#skF_4': $i).
% 3.52/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.52/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.52/1.80  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.52/1.80  
% 3.52/1.82  tff(f_88, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.52/1.82  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.52/1.82  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.52/1.82  tff(f_81, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 3.52/1.82  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.52/1.82  tff(f_53, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.52/1.82  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.52/1.82  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.52/1.82  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.52/1.82  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.52/1.82  tff(f_55, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.52/1.82  tff(f_61, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.52/1.82  tff(c_44, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.52/1.82  tff(c_22, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.52/1.82  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.52/1.82  tff(c_510, plain, (![B_96, A_97]: (k3_xboole_0(B_96, k1_tarski(A_97))=k1_tarski(A_97) | ~r2_hidden(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.52/1.82  tff(c_548, plain, (![A_97, B_2]: (k3_xboole_0(k1_tarski(A_97), B_2)=k1_tarski(A_97) | ~r2_hidden(A_97, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_510])).
% 3.52/1.82  tff(c_268, plain, (![A_78, B_79]: (k5_xboole_0(A_78, k3_xboole_0(A_78, B_79))=k4_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.52/1.82  tff(c_280, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_268])).
% 3.52/1.82  tff(c_12, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.52/1.82  tff(c_85, plain, (![A_61, B_62]: (k4_xboole_0(A_61, k2_xboole_0(A_61, B_62))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.52/1.82  tff(c_92, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_85])).
% 3.52/1.82  tff(c_191, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k4_xboole_0(B_74, A_73))=k2_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.52/1.82  tff(c_203, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=k2_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_92, c_191])).
% 3.52/1.82  tff(c_18, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.52/1.82  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.52/1.82  tff(c_351, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, k3_xboole_0(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.52/1.82  tff(c_396, plain, (![A_92, B_93]: (~r1_xboole_0(A_92, B_93) | k3_xboole_0(A_92, B_93)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_351])).
% 3.52/1.82  tff(c_401, plain, (![A_94]: (k3_xboole_0(A_94, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_396])).
% 3.52/1.82  tff(c_440, plain, (![A_95]: (k3_xboole_0(k1_xboole_0, A_95)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_401, c_2])).
% 3.52/1.82  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.52/1.82  tff(c_455, plain, (![A_95]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_95))), inference(superposition, [status(thm), theory('equality')], [c_440, c_10])).
% 3.52/1.82  tff(c_602, plain, (![A_101]: (k4_xboole_0(k1_xboole_0, A_101)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_203, c_455])).
% 3.52/1.82  tff(c_610, plain, (![A_101]: (k5_xboole_0(A_101, k1_xboole_0)=k2_xboole_0(A_101, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_602, c_22])).
% 3.52/1.82  tff(c_630, plain, (![A_101]: (k5_xboole_0(A_101, k1_xboole_0)=A_101)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_610])).
% 3.52/1.82  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.52/1.82  tff(c_14, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k2_xboole_0(A_13, B_14))=A_13)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.52/1.82  tff(c_286, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k5_xboole_0(A_13, A_13))), inference(superposition, [status(thm), theory('equality')], [c_14, c_268])).
% 3.52/1.82  tff(c_290, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_286])).
% 3.52/1.82  tff(c_699, plain, (![A_105, B_106, C_107]: (k5_xboole_0(k5_xboole_0(A_105, B_106), C_107)=k5_xboole_0(A_105, k5_xboole_0(B_106, C_107)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.52/1.82  tff(c_741, plain, (![A_105, B_106]: (k5_xboole_0(A_105, k5_xboole_0(B_106, k5_xboole_0(A_105, B_106)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_290, c_699])).
% 3.52/1.82  tff(c_409, plain, (![A_94]: (k5_xboole_0(A_94, k1_xboole_0)=k4_xboole_0(A_94, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_401, c_10])).
% 3.52/1.82  tff(c_764, plain, (![A_108]: (k4_xboole_0(A_108, k1_xboole_0)=A_108)), inference(demodulation, [status(thm), theory('equality')], [c_630, c_409])).
% 3.52/1.82  tff(c_774, plain, (![A_108]: (k5_xboole_0(k1_xboole_0, A_108)=k2_xboole_0(k1_xboole_0, A_108))), inference(superposition, [status(thm), theory('equality')], [c_764, c_22])).
% 3.52/1.82  tff(c_737, plain, (![A_13, C_107]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_107))=k5_xboole_0(k1_xboole_0, C_107))), inference(superposition, [status(thm), theory('equality')], [c_290, c_699])).
% 3.52/1.82  tff(c_1133, plain, (![A_143, C_144]: (k5_xboole_0(A_143, k5_xboole_0(A_143, C_144))=k2_xboole_0(k1_xboole_0, C_144))), inference(demodulation, [status(thm), theory('equality')], [c_774, c_737])).
% 3.52/1.82  tff(c_1200, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_13))), inference(superposition, [status(thm), theory('equality')], [c_290, c_1133])).
% 3.52/1.82  tff(c_1221, plain, (![A_13]: (k2_xboole_0(k1_xboole_0, A_13)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_630, c_1200])).
% 3.52/1.82  tff(c_1132, plain, (![A_13, C_107]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_107))=k2_xboole_0(k1_xboole_0, C_107))), inference(demodulation, [status(thm), theory('equality')], [c_774, c_737])).
% 3.52/1.82  tff(c_1362, plain, (![A_154, C_155]: (k5_xboole_0(A_154, k5_xboole_0(A_154, C_155))=C_155)), inference(demodulation, [status(thm), theory('equality')], [c_1221, c_1132])).
% 3.52/1.82  tff(c_1406, plain, (![B_106, A_105]: (k5_xboole_0(B_106, k5_xboole_0(A_105, B_106))=k5_xboole_0(A_105, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_741, c_1362])).
% 3.52/1.82  tff(c_1470, plain, (![B_157, A_158]: (k5_xboole_0(B_157, k5_xboole_0(A_158, B_157))=A_158)), inference(demodulation, [status(thm), theory('equality')], [c_630, c_1406])).
% 3.52/1.82  tff(c_2748, plain, (![A_189, B_190]: (k5_xboole_0(k3_xboole_0(A_189, B_190), k4_xboole_0(B_190, A_189))=B_190)), inference(superposition, [status(thm), theory('equality')], [c_280, c_1470])).
% 3.52/1.82  tff(c_2786, plain, (![A_97, B_2]: (k5_xboole_0(k1_tarski(A_97), k4_xboole_0(B_2, k1_tarski(A_97)))=B_2 | ~r2_hidden(A_97, B_2))), inference(superposition, [status(thm), theory('equality')], [c_548, c_2748])).
% 3.52/1.82  tff(c_2840, plain, (![A_191, B_192]: (k2_xboole_0(k1_tarski(A_191), B_192)=B_192 | ~r2_hidden(A_191, B_192))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2786])).
% 3.52/1.82  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.52/1.82  tff(c_2876, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2840, c_42])).
% 3.52/1.82  tff(c_2903, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_2876])).
% 3.52/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.82  
% 3.52/1.82  Inference rules
% 3.52/1.82  ----------------------
% 3.52/1.82  #Ref     : 0
% 3.52/1.82  #Sup     : 696
% 3.52/1.82  #Fact    : 0
% 3.52/1.82  #Define  : 0
% 3.52/1.82  #Split   : 0
% 3.52/1.82  #Chain   : 0
% 3.52/1.82  #Close   : 0
% 3.52/1.82  
% 3.52/1.82  Ordering : KBO
% 3.52/1.82  
% 3.52/1.82  Simplification rules
% 3.52/1.82  ----------------------
% 3.52/1.82  #Subsume      : 65
% 3.52/1.82  #Demod        : 461
% 3.52/1.82  #Tautology    : 455
% 3.52/1.82  #SimpNegUnit  : 2
% 3.52/1.82  #BackRed      : 11
% 3.52/1.82  
% 3.52/1.82  #Partial instantiations: 0
% 3.52/1.82  #Strategies tried      : 1
% 3.52/1.82  
% 3.52/1.82  Timing (in seconds)
% 3.52/1.82  ----------------------
% 3.52/1.82  Preprocessing        : 0.37
% 3.52/1.82  Parsing              : 0.21
% 3.52/1.82  CNF conversion       : 0.02
% 3.52/1.82  Main loop            : 0.53
% 3.52/1.82  Inferencing          : 0.20
% 3.52/1.82  Reduction            : 0.20
% 3.52/1.82  Demodulation         : 0.16
% 3.52/1.82  BG Simplification    : 0.03
% 3.52/1.82  Subsumption          : 0.07
% 3.52/1.82  Abstraction          : 0.03
% 3.52/1.82  MUC search           : 0.00
% 3.52/1.82  Cooper               : 0.00
% 3.52/1.82  Total                : 0.93
% 3.52/1.82  Index Insertion      : 0.00
% 3.52/1.82  Index Deletion       : 0.00
% 3.52/1.82  Index Matching       : 0.00
% 3.52/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
