%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:11 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 141 expanded)
%              Number of leaves         :   37 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :   96 ( 254 expanded)
%              Number of equality atoms :   70 ( 225 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_52,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_50,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_68,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_56,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_22,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_84,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_22])).

tff(c_451,plain,(
    ! [B_96,A_97] :
      ( k1_tarski(B_96) = A_97
      | k1_xboole_0 = A_97
      | ~ r1_tarski(A_97,k1_tarski(B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_458,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_84,c_451])).

tff(c_469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_68,c_458])).

tff(c_470,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_471,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_18,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_472,plain,(
    ! [A_16] : k5_xboole_0(A_16,'#skF_4') = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_474,plain,(
    ! [A_17] : r1_xboole_0(A_17,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_20])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_618,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | A_10 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_10])).

tff(c_730,plain,(
    ! [A_122,B_123,C_124] :
      ( ~ r1_xboole_0(A_122,B_123)
      | ~ r2_hidden(C_124,k3_xboole_0(A_122,B_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_742,plain,(
    ! [A_125,B_126] :
      ( ~ r1_xboole_0(A_125,B_126)
      | k3_xboole_0(A_125,B_126) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_618,c_730])).

tff(c_747,plain,(
    ! [A_127] : k3_xboole_0(A_127,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_474,c_742])).

tff(c_764,plain,(
    ! [A_1] : k3_xboole_0('#skF_4',A_1) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_747])).

tff(c_531,plain,(
    ! [B_103,A_104] : k5_xboole_0(B_103,A_104) = k5_xboole_0(A_104,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_547,plain,(
    ! [A_104] : k5_xboole_0('#skF_4',A_104) = A_104 ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_472])).

tff(c_993,plain,(
    ! [A_146,B_147] : k5_xboole_0(k5_xboole_0(A_146,B_147),k3_xboole_0(A_146,B_147)) = k2_xboole_0(A_146,B_147) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1026,plain,(
    ! [A_104] : k5_xboole_0(A_104,k3_xboole_0('#skF_4',A_104)) = k2_xboole_0('#skF_4',A_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_547,c_993])).

tff(c_1054,plain,(
    ! [A_104] : k2_xboole_0('#skF_4',A_104) = A_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_764,c_1026])).

tff(c_1083,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1054,c_56])).

tff(c_1085,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_470,c_1083])).

tff(c_1086,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1087,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1116,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_1087,c_54])).

tff(c_1104,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_56])).

tff(c_1424,plain,(
    ! [A_178,B_179] : k5_xboole_0(A_178,k3_xboole_0(A_178,B_179)) = k4_xboole_0(A_178,B_179) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1440,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1424])).

tff(c_1970,plain,(
    ! [A_212,B_213] : k5_xboole_0(k5_xboole_0(A_212,B_213),k3_xboole_0(A_212,B_213)) = k2_xboole_0(A_212,B_213) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    ! [A_20,B_21,C_22] : k5_xboole_0(k5_xboole_0(A_20,B_21),C_22) = k5_xboole_0(A_20,k5_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1982,plain,(
    ! [A_212,B_213] : k5_xboole_0(A_212,k5_xboole_0(B_213,k3_xboole_0(A_212,B_213))) = k2_xboole_0(A_212,B_213) ),
    inference(superposition,[status(thm),theory(equality)],[c_1970,c_24])).

tff(c_2040,plain,(
    ! [A_212,B_213] : k5_xboole_0(A_212,k4_xboole_0(B_213,A_212)) = k2_xboole_0(A_212,B_213) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1440,c_1982])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1761,plain,(
    ! [A_196,B_197,C_198] : k5_xboole_0(k5_xboole_0(A_196,B_197),C_198) = k5_xboole_0(A_196,k5_xboole_0(B_197,C_198)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2363,plain,(
    ! [A_234,B_235,C_236] : k5_xboole_0(k5_xboole_0(A_234,B_235),C_236) = k5_xboole_0(B_235,k5_xboole_0(A_234,C_236)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1761])).

tff(c_26,plain,(
    ! [A_23,B_24] : k5_xboole_0(k5_xboole_0(A_23,B_24),k3_xboole_0(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2380,plain,(
    ! [B_235,A_234] : k5_xboole_0(B_235,k5_xboole_0(A_234,k3_xboole_0(A_234,B_235))) = k2_xboole_0(A_234,B_235) ),
    inference(superposition,[status(thm),theory(equality)],[c_2363,c_26])).

tff(c_2492,plain,(
    ! [B_243,A_244] : k2_xboole_0(B_243,A_244) = k2_xboole_0(A_244,B_243) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2040,c_16,c_2380])).

tff(c_2593,plain,(
    ! [A_245,B_246] : r1_tarski(A_245,k2_xboole_0(B_246,A_245)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2492,c_22])).

tff(c_2617,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1104,c_2593])).

tff(c_1587,plain,(
    ! [B_189,A_190] :
      ( k1_tarski(B_189) = A_190
      | k1_xboole_0 = A_190
      | ~ r1_tarski(A_190,k1_tarski(B_189)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1597,plain,(
    ! [A_190] :
      ( k1_tarski('#skF_3') = A_190
      | k1_xboole_0 = A_190
      | ~ r1_tarski(A_190,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1087,c_1587])).

tff(c_1604,plain,(
    ! [A_190] :
      ( A_190 = '#skF_4'
      | k1_xboole_0 = A_190
      | ~ r1_tarski(A_190,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_1597])).

tff(c_2627,plain,
    ( '#skF_5' = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2617,c_1604])).

tff(c_2634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1086,c_1116,c_2627])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.59  
% 3.42/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.59  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 3.42/1.59  
% 3.42/1.59  %Foreground sorts:
% 3.42/1.59  
% 3.42/1.59  
% 3.42/1.59  %Background operators:
% 3.42/1.59  
% 3.42/1.59  
% 3.42/1.59  %Foreground operators:
% 3.42/1.59  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.42/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.42/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.42/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.42/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.42/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.42/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.42/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.42/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.42/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.42/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.42/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.42/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.42/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.42/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.42/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.42/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.42/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.42/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.42/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.42/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.42/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.42/1.59  
% 3.42/1.60  tff(f_108, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.42/1.60  tff(f_63, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.42/1.60  tff(f_87, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.42/1.60  tff(f_59, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.42/1.60  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.42/1.60  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.42/1.60  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.42/1.60  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.42/1.60  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.42/1.60  tff(f_67, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.42/1.60  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.42/1.60  tff(f_65, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.42/1.60  tff(c_52, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.42/1.60  tff(c_80, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_52])).
% 3.42/1.60  tff(c_50, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.42/1.60  tff(c_68, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_50])).
% 3.42/1.60  tff(c_56, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.42/1.60  tff(c_22, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.42/1.60  tff(c_84, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_22])).
% 3.42/1.60  tff(c_451, plain, (![B_96, A_97]: (k1_tarski(B_96)=A_97 | k1_xboole_0=A_97 | ~r1_tarski(A_97, k1_tarski(B_96)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.42/1.60  tff(c_458, plain, (k1_tarski('#skF_3')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_84, c_451])).
% 3.42/1.60  tff(c_469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_68, c_458])).
% 3.42/1.60  tff(c_470, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_52])).
% 3.42/1.60  tff(c_471, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_52])).
% 3.42/1.60  tff(c_18, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.42/1.60  tff(c_472, plain, (![A_16]: (k5_xboole_0(A_16, '#skF_4')=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_471, c_18])).
% 3.42/1.60  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.42/1.60  tff(c_20, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.42/1.60  tff(c_474, plain, (![A_17]: (r1_xboole_0(A_17, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_471, c_20])).
% 3.42/1.60  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.42/1.60  tff(c_618, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | A_10='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_471, c_10])).
% 3.42/1.60  tff(c_730, plain, (![A_122, B_123, C_124]: (~r1_xboole_0(A_122, B_123) | ~r2_hidden(C_124, k3_xboole_0(A_122, B_123)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.42/1.60  tff(c_742, plain, (![A_125, B_126]: (~r1_xboole_0(A_125, B_126) | k3_xboole_0(A_125, B_126)='#skF_4')), inference(resolution, [status(thm)], [c_618, c_730])).
% 3.42/1.60  tff(c_747, plain, (![A_127]: (k3_xboole_0(A_127, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_474, c_742])).
% 3.42/1.60  tff(c_764, plain, (![A_1]: (k3_xboole_0('#skF_4', A_1)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2, c_747])).
% 3.42/1.60  tff(c_531, plain, (![B_103, A_104]: (k5_xboole_0(B_103, A_104)=k5_xboole_0(A_104, B_103))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.42/1.60  tff(c_547, plain, (![A_104]: (k5_xboole_0('#skF_4', A_104)=A_104)), inference(superposition, [status(thm), theory('equality')], [c_531, c_472])).
% 3.42/1.60  tff(c_993, plain, (![A_146, B_147]: (k5_xboole_0(k5_xboole_0(A_146, B_147), k3_xboole_0(A_146, B_147))=k2_xboole_0(A_146, B_147))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.42/1.60  tff(c_1026, plain, (![A_104]: (k5_xboole_0(A_104, k3_xboole_0('#skF_4', A_104))=k2_xboole_0('#skF_4', A_104))), inference(superposition, [status(thm), theory('equality')], [c_547, c_993])).
% 3.42/1.60  tff(c_1054, plain, (![A_104]: (k2_xboole_0('#skF_4', A_104)=A_104)), inference(demodulation, [status(thm), theory('equality')], [c_472, c_764, c_1026])).
% 3.42/1.60  tff(c_1083, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1054, c_56])).
% 3.42/1.60  tff(c_1085, plain, $false, inference(negUnitSimplification, [status(thm)], [c_470, c_1083])).
% 3.42/1.60  tff(c_1086, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_50])).
% 3.42/1.60  tff(c_1087, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_50])).
% 3.42/1.60  tff(c_54, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.42/1.60  tff(c_1116, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_1087, c_54])).
% 3.42/1.60  tff(c_1104, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_56])).
% 3.42/1.60  tff(c_1424, plain, (![A_178, B_179]: (k5_xboole_0(A_178, k3_xboole_0(A_178, B_179))=k4_xboole_0(A_178, B_179))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.42/1.60  tff(c_1440, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1424])).
% 3.42/1.60  tff(c_1970, plain, (![A_212, B_213]: (k5_xboole_0(k5_xboole_0(A_212, B_213), k3_xboole_0(A_212, B_213))=k2_xboole_0(A_212, B_213))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.42/1.60  tff(c_24, plain, (![A_20, B_21, C_22]: (k5_xboole_0(k5_xboole_0(A_20, B_21), C_22)=k5_xboole_0(A_20, k5_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.42/1.60  tff(c_1982, plain, (![A_212, B_213]: (k5_xboole_0(A_212, k5_xboole_0(B_213, k3_xboole_0(A_212, B_213)))=k2_xboole_0(A_212, B_213))), inference(superposition, [status(thm), theory('equality')], [c_1970, c_24])).
% 3.42/1.60  tff(c_2040, plain, (![A_212, B_213]: (k5_xboole_0(A_212, k4_xboole_0(B_213, A_212))=k2_xboole_0(A_212, B_213))), inference(demodulation, [status(thm), theory('equality')], [c_1440, c_1982])).
% 3.42/1.60  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.42/1.60  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.42/1.60  tff(c_1761, plain, (![A_196, B_197, C_198]: (k5_xboole_0(k5_xboole_0(A_196, B_197), C_198)=k5_xboole_0(A_196, k5_xboole_0(B_197, C_198)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.42/1.60  tff(c_2363, plain, (![A_234, B_235, C_236]: (k5_xboole_0(k5_xboole_0(A_234, B_235), C_236)=k5_xboole_0(B_235, k5_xboole_0(A_234, C_236)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1761])).
% 3.42/1.60  tff(c_26, plain, (![A_23, B_24]: (k5_xboole_0(k5_xboole_0(A_23, B_24), k3_xboole_0(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.42/1.60  tff(c_2380, plain, (![B_235, A_234]: (k5_xboole_0(B_235, k5_xboole_0(A_234, k3_xboole_0(A_234, B_235)))=k2_xboole_0(A_234, B_235))), inference(superposition, [status(thm), theory('equality')], [c_2363, c_26])).
% 3.42/1.60  tff(c_2492, plain, (![B_243, A_244]: (k2_xboole_0(B_243, A_244)=k2_xboole_0(A_244, B_243))), inference(demodulation, [status(thm), theory('equality')], [c_2040, c_16, c_2380])).
% 3.42/1.60  tff(c_2593, plain, (![A_245, B_246]: (r1_tarski(A_245, k2_xboole_0(B_246, A_245)))), inference(superposition, [status(thm), theory('equality')], [c_2492, c_22])).
% 3.42/1.60  tff(c_2617, plain, (r1_tarski('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1104, c_2593])).
% 3.42/1.60  tff(c_1587, plain, (![B_189, A_190]: (k1_tarski(B_189)=A_190 | k1_xboole_0=A_190 | ~r1_tarski(A_190, k1_tarski(B_189)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.42/1.60  tff(c_1597, plain, (![A_190]: (k1_tarski('#skF_3')=A_190 | k1_xboole_0=A_190 | ~r1_tarski(A_190, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1087, c_1587])).
% 3.42/1.60  tff(c_1604, plain, (![A_190]: (A_190='#skF_4' | k1_xboole_0=A_190 | ~r1_tarski(A_190, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_1597])).
% 3.42/1.60  tff(c_2627, plain, ('#skF_5'='#skF_4' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2617, c_1604])).
% 3.42/1.60  tff(c_2634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1086, c_1116, c_2627])).
% 3.42/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.60  
% 3.42/1.60  Inference rules
% 3.42/1.60  ----------------------
% 3.42/1.60  #Ref     : 0
% 3.42/1.60  #Sup     : 618
% 3.42/1.60  #Fact    : 0
% 3.42/1.60  #Define  : 0
% 3.42/1.60  #Split   : 3
% 3.42/1.60  #Chain   : 0
% 3.42/1.60  #Close   : 0
% 3.42/1.60  
% 3.42/1.60  Ordering : KBO
% 3.42/1.60  
% 3.42/1.60  Simplification rules
% 3.42/1.60  ----------------------
% 3.42/1.60  #Subsume      : 21
% 3.42/1.60  #Demod        : 277
% 3.42/1.60  #Tautology    : 444
% 3.42/1.60  #SimpNegUnit  : 12
% 3.42/1.60  #BackRed      : 11
% 3.42/1.60  
% 3.42/1.60  #Partial instantiations: 0
% 3.42/1.60  #Strategies tried      : 1
% 3.42/1.60  
% 3.42/1.60  Timing (in seconds)
% 3.42/1.60  ----------------------
% 3.42/1.61  Preprocessing        : 0.32
% 3.42/1.61  Parsing              : 0.17
% 3.42/1.61  CNF conversion       : 0.02
% 3.42/1.61  Main loop            : 0.52
% 3.42/1.61  Inferencing          : 0.19
% 3.42/1.61  Reduction            : 0.19
% 3.42/1.61  Demodulation         : 0.15
% 3.42/1.61  BG Simplification    : 0.03
% 3.42/1.61  Subsumption          : 0.07
% 3.42/1.61  Abstraction          : 0.02
% 3.42/1.61  MUC search           : 0.00
% 3.42/1.61  Cooper               : 0.00
% 3.42/1.61  Total                : 0.87
% 3.42/1.61  Index Insertion      : 0.00
% 3.42/1.61  Index Deletion       : 0.00
% 3.42/1.61  Index Matching       : 0.00
% 3.42/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
