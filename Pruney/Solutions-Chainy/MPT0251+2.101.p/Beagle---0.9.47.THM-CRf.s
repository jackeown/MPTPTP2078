%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:00 EST 2020

% Result     : Theorem 5.88s
% Output     : CNFRefutation 6.11s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 187 expanded)
%              Number of leaves         :   38 (  79 expanded)
%              Depth                    :   15
%              Number of atoms          :   73 ( 215 expanded)
%              Number of equality atoms :   48 ( 134 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_69,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_71,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_93,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_56,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32,plain,(
    ! [A_29,B_30] : k5_xboole_0(A_29,k4_xboole_0(B_30,A_29)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    ! [A_24] : k5_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k2_xboole_0(A_20,B_21)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    ! [A_16,B_17] : k3_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_611,plain,(
    ! [A_118,B_119] : k5_xboole_0(A_118,k3_xboole_0(A_118,B_119)) = k4_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_623,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k5_xboole_0(A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_611])).

tff(c_633,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_623])).

tff(c_766,plain,(
    ! [A_131,B_132,C_133] : k5_xboole_0(k5_xboole_0(A_131,B_132),C_133) = k5_xboole_0(A_131,k5_xboole_0(B_132,C_133)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_801,plain,(
    ! [A_131,B_132] : k5_xboole_0(A_131,k5_xboole_0(B_132,k5_xboole_0(A_131,B_132))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_766])).

tff(c_28,plain,(
    ! [A_25] : r1_xboole_0(A_25,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_535,plain,(
    ! [A_113,B_114,C_115] :
      ( ~ r1_xboole_0(A_113,B_114)
      | ~ r2_hidden(C_115,k3_xboole_0(A_113,B_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_829,plain,(
    ! [A_134,B_135] :
      ( ~ r1_xboole_0(A_134,B_135)
      | k3_xboole_0(A_134,B_135) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_535])).

tff(c_833,plain,(
    ! [A_25] : k3_xboole_0(A_25,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_829])).

tff(c_834,plain,(
    ! [A_136] : k3_xboole_0(A_136,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_829])).

tff(c_14,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_845,plain,(
    ! [A_136] : k5_xboole_0(A_136,k1_xboole_0) = k4_xboole_0(A_136,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_834,c_14])).

tff(c_994,plain,(
    ! [A_139] : k4_xboole_0(A_139,k1_xboole_0) = A_139 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_845])).

tff(c_24,plain,(
    ! [A_22,B_23] : k2_xboole_0(k3_xboole_0(A_22,B_23),k4_xboole_0(A_22,B_23)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1003,plain,(
    ! [A_139] : k2_xboole_0(k3_xboole_0(A_139,k1_xboole_0),A_139) = A_139 ),
    inference(superposition,[status(thm),theory(equality)],[c_994,c_24])).

tff(c_1032,plain,(
    ! [A_139] : k2_xboole_0(k1_xboole_0,A_139) = A_139 ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_1003])).

tff(c_1000,plain,(
    ! [A_139] : k5_xboole_0(k1_xboole_0,A_139) = k2_xboole_0(k1_xboole_0,A_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_994,c_32])).

tff(c_1213,plain,(
    ! [A_139] : k5_xboole_0(k1_xboole_0,A_139) = A_139 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_1000])).

tff(c_797,plain,(
    ! [A_16,C_133] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_133)) = k5_xboole_0(k1_xboole_0,C_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_766])).

tff(c_2497,plain,(
    ! [A_208,C_209] : k5_xboole_0(A_208,k5_xboole_0(A_208,C_209)) = C_209 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1213,c_797])).

tff(c_2534,plain,(
    ! [B_132,A_131] : k5_xboole_0(B_132,k5_xboole_0(A_131,B_132)) = k5_xboole_0(A_131,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_801,c_2497])).

tff(c_2587,plain,(
    ! [B_210,A_211] : k5_xboole_0(B_210,k5_xboole_0(A_211,B_210)) = A_211 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2534])).

tff(c_2496,plain,(
    ! [A_16,C_133] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_133)) = C_133 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1213,c_797])).

tff(c_2596,plain,(
    ! [B_210,A_211] : k5_xboole_0(B_210,A_211) = k5_xboole_0(A_211,B_210) ),
    inference(superposition,[status(thm),theory(equality)],[c_2587,c_2496])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(k1_tarski(A_59),B_60)
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_152,plain,(
    ! [A_82,B_83] :
      ( k3_xboole_0(A_82,B_83) = A_82
      | ~ r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2177,plain,(
    ! [A_201,B_202] :
      ( k3_xboole_0(k1_tarski(A_201),B_202) = k1_tarski(A_201)
      | ~ r2_hidden(A_201,B_202) ) ),
    inference(resolution,[status(thm)],[c_50,c_152])).

tff(c_7143,plain,(
    ! [A_285,A_286] :
      ( k3_xboole_0(A_285,k1_tarski(A_286)) = k1_tarski(A_286)
      | ~ r2_hidden(A_286,A_285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2177])).

tff(c_4419,plain,(
    ! [A_241,B_242,C_243] : k5_xboole_0(A_241,k5_xboole_0(k3_xboole_0(A_241,B_242),C_243)) = k5_xboole_0(k4_xboole_0(A_241,B_242),C_243) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_766])).

tff(c_4537,plain,(
    ! [A_241,B_242] : k5_xboole_0(k4_xboole_0(A_241,B_242),k3_xboole_0(A_241,B_242)) = k5_xboole_0(A_241,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_4419])).

tff(c_4577,plain,(
    ! [A_241,B_242] : k5_xboole_0(k4_xboole_0(A_241,B_242),k3_xboole_0(A_241,B_242)) = A_241 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4537])).

tff(c_7177,plain,(
    ! [A_285,A_286] :
      ( k5_xboole_0(k4_xboole_0(A_285,k1_tarski(A_286)),k1_tarski(A_286)) = A_285
      | ~ r2_hidden(A_286,A_285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7143,c_4577])).

tff(c_7653,plain,(
    ! [A_291,A_292] :
      ( k2_xboole_0(k1_tarski(A_291),A_292) = A_292
      | ~ r2_hidden(A_291,A_292) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2596,c_7177])).

tff(c_54,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_7719,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7653,c_54])).

tff(c_7754,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_7719])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:01:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.88/2.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.88/2.28  
% 5.88/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.88/2.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.88/2.28  
% 5.88/2.28  %Foreground sorts:
% 5.88/2.28  
% 5.88/2.28  
% 5.88/2.28  %Background operators:
% 5.88/2.28  
% 5.88/2.28  
% 5.88/2.28  %Foreground operators:
% 5.88/2.28  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.88/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.88/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.88/2.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.88/2.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.88/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.88/2.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.88/2.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.88/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.88/2.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.88/2.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.88/2.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.88/2.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.88/2.28  tff('#skF_3', type, '#skF_3': $i).
% 5.88/2.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.88/2.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.88/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.88/2.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.88/2.28  tff('#skF_4', type, '#skF_4': $i).
% 5.88/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.88/2.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.88/2.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.88/2.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.88/2.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.88/2.28  
% 6.11/2.30  tff(f_100, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 6.11/2.30  tff(f_75, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.11/2.30  tff(f_69, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.11/2.30  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 6.11/2.30  tff(f_59, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 6.11/2.30  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.11/2.30  tff(f_73, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.11/2.30  tff(f_71, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 6.11/2.30  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.11/2.30  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.11/2.30  tff(f_67, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 6.11/2.30  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.11/2.30  tff(f_93, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.11/2.30  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.11/2.30  tff(c_56, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.11/2.30  tff(c_32, plain, (![A_29, B_30]: (k5_xboole_0(A_29, k4_xboole_0(B_30, A_29))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.11/2.30  tff(c_26, plain, (![A_24]: (k5_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.11/2.30  tff(c_22, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k2_xboole_0(A_20, B_21))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.11/2.30  tff(c_18, plain, (![A_16, B_17]: (k3_xboole_0(A_16, k2_xboole_0(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.11/2.30  tff(c_611, plain, (![A_118, B_119]: (k5_xboole_0(A_118, k3_xboole_0(A_118, B_119))=k4_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.11/2.30  tff(c_623, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k5_xboole_0(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_18, c_611])).
% 6.11/2.30  tff(c_633, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_623])).
% 6.11/2.30  tff(c_766, plain, (![A_131, B_132, C_133]: (k5_xboole_0(k5_xboole_0(A_131, B_132), C_133)=k5_xboole_0(A_131, k5_xboole_0(B_132, C_133)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.11/2.30  tff(c_801, plain, (![A_131, B_132]: (k5_xboole_0(A_131, k5_xboole_0(B_132, k5_xboole_0(A_131, B_132)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_633, c_766])).
% 6.11/2.30  tff(c_28, plain, (![A_25]: (r1_xboole_0(A_25, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.11/2.30  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.11/2.30  tff(c_535, plain, (![A_113, B_114, C_115]: (~r1_xboole_0(A_113, B_114) | ~r2_hidden(C_115, k3_xboole_0(A_113, B_114)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.11/2.30  tff(c_829, plain, (![A_134, B_135]: (~r1_xboole_0(A_134, B_135) | k3_xboole_0(A_134, B_135)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_535])).
% 6.11/2.30  tff(c_833, plain, (![A_25]: (k3_xboole_0(A_25, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_829])).
% 6.11/2.30  tff(c_834, plain, (![A_136]: (k3_xboole_0(A_136, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_829])).
% 6.11/2.30  tff(c_14, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.11/2.30  tff(c_845, plain, (![A_136]: (k5_xboole_0(A_136, k1_xboole_0)=k4_xboole_0(A_136, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_834, c_14])).
% 6.11/2.30  tff(c_994, plain, (![A_139]: (k4_xboole_0(A_139, k1_xboole_0)=A_139)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_845])).
% 6.11/2.30  tff(c_24, plain, (![A_22, B_23]: (k2_xboole_0(k3_xboole_0(A_22, B_23), k4_xboole_0(A_22, B_23))=A_22)), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.11/2.30  tff(c_1003, plain, (![A_139]: (k2_xboole_0(k3_xboole_0(A_139, k1_xboole_0), A_139)=A_139)), inference(superposition, [status(thm), theory('equality')], [c_994, c_24])).
% 6.11/2.30  tff(c_1032, plain, (![A_139]: (k2_xboole_0(k1_xboole_0, A_139)=A_139)), inference(demodulation, [status(thm), theory('equality')], [c_833, c_1003])).
% 6.11/2.30  tff(c_1000, plain, (![A_139]: (k5_xboole_0(k1_xboole_0, A_139)=k2_xboole_0(k1_xboole_0, A_139))), inference(superposition, [status(thm), theory('equality')], [c_994, c_32])).
% 6.11/2.30  tff(c_1213, plain, (![A_139]: (k5_xboole_0(k1_xboole_0, A_139)=A_139)), inference(demodulation, [status(thm), theory('equality')], [c_1032, c_1000])).
% 6.11/2.30  tff(c_797, plain, (![A_16, C_133]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_133))=k5_xboole_0(k1_xboole_0, C_133))), inference(superposition, [status(thm), theory('equality')], [c_633, c_766])).
% 6.11/2.30  tff(c_2497, plain, (![A_208, C_209]: (k5_xboole_0(A_208, k5_xboole_0(A_208, C_209))=C_209)), inference(demodulation, [status(thm), theory('equality')], [c_1213, c_797])).
% 6.11/2.30  tff(c_2534, plain, (![B_132, A_131]: (k5_xboole_0(B_132, k5_xboole_0(A_131, B_132))=k5_xboole_0(A_131, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_801, c_2497])).
% 6.11/2.30  tff(c_2587, plain, (![B_210, A_211]: (k5_xboole_0(B_210, k5_xboole_0(A_211, B_210))=A_211)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2534])).
% 6.11/2.30  tff(c_2496, plain, (![A_16, C_133]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_133))=C_133)), inference(demodulation, [status(thm), theory('equality')], [c_1213, c_797])).
% 6.11/2.30  tff(c_2596, plain, (![B_210, A_211]: (k5_xboole_0(B_210, A_211)=k5_xboole_0(A_211, B_210))), inference(superposition, [status(thm), theory('equality')], [c_2587, c_2496])).
% 6.11/2.30  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.11/2.30  tff(c_50, plain, (![A_59, B_60]: (r1_tarski(k1_tarski(A_59), B_60) | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.11/2.30  tff(c_152, plain, (![A_82, B_83]: (k3_xboole_0(A_82, B_83)=A_82 | ~r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.11/2.30  tff(c_2177, plain, (![A_201, B_202]: (k3_xboole_0(k1_tarski(A_201), B_202)=k1_tarski(A_201) | ~r2_hidden(A_201, B_202))), inference(resolution, [status(thm)], [c_50, c_152])).
% 6.11/2.30  tff(c_7143, plain, (![A_285, A_286]: (k3_xboole_0(A_285, k1_tarski(A_286))=k1_tarski(A_286) | ~r2_hidden(A_286, A_285))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2177])).
% 6.11/2.30  tff(c_4419, plain, (![A_241, B_242, C_243]: (k5_xboole_0(A_241, k5_xboole_0(k3_xboole_0(A_241, B_242), C_243))=k5_xboole_0(k4_xboole_0(A_241, B_242), C_243))), inference(superposition, [status(thm), theory('equality')], [c_14, c_766])).
% 6.11/2.30  tff(c_4537, plain, (![A_241, B_242]: (k5_xboole_0(k4_xboole_0(A_241, B_242), k3_xboole_0(A_241, B_242))=k5_xboole_0(A_241, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_633, c_4419])).
% 6.11/2.30  tff(c_4577, plain, (![A_241, B_242]: (k5_xboole_0(k4_xboole_0(A_241, B_242), k3_xboole_0(A_241, B_242))=A_241)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4537])).
% 6.11/2.30  tff(c_7177, plain, (![A_285, A_286]: (k5_xboole_0(k4_xboole_0(A_285, k1_tarski(A_286)), k1_tarski(A_286))=A_285 | ~r2_hidden(A_286, A_285))), inference(superposition, [status(thm), theory('equality')], [c_7143, c_4577])).
% 6.11/2.30  tff(c_7653, plain, (![A_291, A_292]: (k2_xboole_0(k1_tarski(A_291), A_292)=A_292 | ~r2_hidden(A_291, A_292))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2596, c_7177])).
% 6.11/2.30  tff(c_54, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.11/2.30  tff(c_7719, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7653, c_54])).
% 6.11/2.30  tff(c_7754, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_7719])).
% 6.11/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.11/2.30  
% 6.11/2.30  Inference rules
% 6.11/2.30  ----------------------
% 6.11/2.30  #Ref     : 0
% 6.11/2.30  #Sup     : 1895
% 6.11/2.30  #Fact    : 0
% 6.11/2.30  #Define  : 0
% 6.11/2.30  #Split   : 0
% 6.11/2.30  #Chain   : 0
% 6.11/2.30  #Close   : 0
% 6.11/2.30  
% 6.11/2.30  Ordering : KBO
% 6.11/2.30  
% 6.11/2.30  Simplification rules
% 6.11/2.30  ----------------------
% 6.11/2.30  #Subsume      : 160
% 6.11/2.30  #Demod        : 1914
% 6.11/2.30  #Tautology    : 1179
% 6.11/2.30  #SimpNegUnit  : 13
% 6.11/2.30  #BackRed      : 6
% 6.11/2.30  
% 6.11/2.30  #Partial instantiations: 0
% 6.11/2.30  #Strategies tried      : 1
% 6.11/2.30  
% 6.11/2.30  Timing (in seconds)
% 6.11/2.30  ----------------------
% 6.11/2.30  Preprocessing        : 0.37
% 6.11/2.30  Parsing              : 0.20
% 6.11/2.30  CNF conversion       : 0.02
% 6.11/2.30  Main loop            : 1.12
% 6.11/2.30  Inferencing          : 0.33
% 6.11/2.30  Reduction            : 0.52
% 6.11/2.30  Demodulation         : 0.43
% 6.11/2.30  BG Simplification    : 0.04
% 6.11/2.30  Subsumption          : 0.16
% 6.11/2.30  Abstraction          : 0.06
% 6.11/2.30  MUC search           : 0.00
% 6.11/2.30  Cooper               : 0.00
% 6.11/2.30  Total                : 1.52
% 6.11/2.30  Index Insertion      : 0.00
% 6.11/2.30  Index Deletion       : 0.00
% 6.11/2.30  Index Matching       : 0.00
% 6.11/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
