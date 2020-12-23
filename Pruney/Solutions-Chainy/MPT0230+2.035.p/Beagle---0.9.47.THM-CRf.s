%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:01 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   72 (  95 expanded)
%              Number of leaves         :   36 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :   64 ( 101 expanded)
%              Number of equality atoms :   52 (  79 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_68,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_66,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_64,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_52,plain,(
    ! [A_40,B_41,C_42] : k2_enumset1(A_40,A_40,B_41,C_42) = k1_enumset1(A_40,B_41,C_42) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_50,plain,(
    ! [A_38,B_39] : k1_enumset1(A_38,A_38,B_39) = k2_tarski(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1183,plain,(
    ! [A_132,B_133,C_134,D_135] : k2_xboole_0(k1_enumset1(A_132,B_133,C_134),k1_tarski(D_135)) = k2_enumset1(A_132,B_133,C_134,D_135) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1222,plain,(
    ! [A_38,B_39,D_135] : k2_xboole_0(k2_tarski(A_38,B_39),k1_tarski(D_135)) = k2_enumset1(A_38,A_38,B_39,D_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1183])).

tff(c_1323,plain,(
    ! [A_142,B_143,D_144] : k2_xboole_0(k2_tarski(A_142,B_143),k1_tarski(D_144)) = k1_enumset1(A_142,B_143,D_144) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1222])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_157,plain,(
    ! [A_88,B_89] :
      ( k3_xboole_0(A_88,B_89) = A_88
      | ~ r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_166,plain,(
    ! [A_90] : k3_xboole_0(k1_xboole_0,A_90) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_157])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_171,plain,(
    ! [A_90] : k3_xboole_0(A_90,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_2])).

tff(c_559,plain,(
    ! [A_108,B_109] : k5_xboole_0(A_108,k3_xboole_0(A_108,B_109)) = k4_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_571,plain,(
    ! [A_90] : k5_xboole_0(A_90,k1_xboole_0) = k4_xboole_0(A_90,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_559])).

tff(c_613,plain,(
    ! [A_111] : k4_xboole_0(A_111,k1_xboole_0) = A_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_571])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_626,plain,(
    ! [A_111] : k4_xboole_0(A_111,A_111) = k3_xboole_0(A_111,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_12])).

tff(c_636,plain,(
    ! [A_111] : k4_xboole_0(A_111,A_111) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_626])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_583,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_559])).

tff(c_704,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_583])).

tff(c_68,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_164,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_157])).

tff(c_568,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_559])).

tff(c_705,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_568])).

tff(c_16,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_775,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_3')) = k5_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_16])).

tff(c_781,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_3')) = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_775])).

tff(c_1329,plain,(
    k1_enumset1('#skF_4','#skF_5','#skF_3') = k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1323,c_781])).

tff(c_20,plain,(
    ! [E_21,A_15,B_16] : r2_hidden(E_21,k1_enumset1(A_15,B_16,E_21)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1363,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1329,c_20])).

tff(c_1273,plain,(
    ! [E_138,C_139,B_140,A_141] :
      ( E_138 = C_139
      | E_138 = B_140
      | E_138 = A_141
      | ~ r2_hidden(E_138,k1_enumset1(A_141,B_140,C_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1517,plain,(
    ! [E_162,B_163,A_164] :
      ( E_162 = B_163
      | E_162 = A_164
      | E_162 = A_164
      | ~ r2_hidden(E_162,k2_tarski(A_164,B_163)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1273])).

tff(c_1520,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1363,c_1517])).

tff(c_1533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_66,c_64,c_1520])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:37:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.52  
% 3.19/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.52  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.19/1.52  
% 3.19/1.52  %Foreground sorts:
% 3.19/1.52  
% 3.19/1.52  
% 3.19/1.52  %Background operators:
% 3.19/1.52  
% 3.19/1.52  
% 3.19/1.52  %Foreground operators:
% 3.19/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.19/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.19/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.19/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.19/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.19/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.19/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.19/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.19/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.19/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.19/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.19/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.19/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.19/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.19/1.52  
% 3.42/1.54  tff(f_90, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.42/1.54  tff(f_70, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.42/1.54  tff(f_68, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.42/1.54  tff(f_64, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 3.42/1.54  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.42/1.54  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.42/1.54  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.42/1.54  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.42/1.54  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.42/1.54  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.42/1.54  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.42/1.54  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.42/1.54  tff(f_58, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.42/1.54  tff(c_66, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.42/1.54  tff(c_64, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.42/1.54  tff(c_52, plain, (![A_40, B_41, C_42]: (k2_enumset1(A_40, A_40, B_41, C_42)=k1_enumset1(A_40, B_41, C_42))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.42/1.54  tff(c_50, plain, (![A_38, B_39]: (k1_enumset1(A_38, A_38, B_39)=k2_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.42/1.54  tff(c_1183, plain, (![A_132, B_133, C_134, D_135]: (k2_xboole_0(k1_enumset1(A_132, B_133, C_134), k1_tarski(D_135))=k2_enumset1(A_132, B_133, C_134, D_135))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.42/1.54  tff(c_1222, plain, (![A_38, B_39, D_135]: (k2_xboole_0(k2_tarski(A_38, B_39), k1_tarski(D_135))=k2_enumset1(A_38, A_38, B_39, D_135))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1183])).
% 3.42/1.54  tff(c_1323, plain, (![A_142, B_143, D_144]: (k2_xboole_0(k2_tarski(A_142, B_143), k1_tarski(D_144))=k1_enumset1(A_142, B_143, D_144))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1222])).
% 3.42/1.54  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.42/1.54  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.42/1.54  tff(c_157, plain, (![A_88, B_89]: (k3_xboole_0(A_88, B_89)=A_88 | ~r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.42/1.54  tff(c_166, plain, (![A_90]: (k3_xboole_0(k1_xboole_0, A_90)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_157])).
% 3.42/1.54  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.42/1.54  tff(c_171, plain, (![A_90]: (k3_xboole_0(A_90, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_166, c_2])).
% 3.42/1.54  tff(c_559, plain, (![A_108, B_109]: (k5_xboole_0(A_108, k3_xboole_0(A_108, B_109))=k4_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.42/1.54  tff(c_571, plain, (![A_90]: (k5_xboole_0(A_90, k1_xboole_0)=k4_xboole_0(A_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_171, c_559])).
% 3.42/1.54  tff(c_613, plain, (![A_111]: (k4_xboole_0(A_111, k1_xboole_0)=A_111)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_571])).
% 3.42/1.54  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.42/1.54  tff(c_626, plain, (![A_111]: (k4_xboole_0(A_111, A_111)=k3_xboole_0(A_111, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_613, c_12])).
% 3.42/1.54  tff(c_636, plain, (![A_111]: (k4_xboole_0(A_111, A_111)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_171, c_626])).
% 3.42/1.54  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.42/1.54  tff(c_583, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_559])).
% 3.42/1.54  tff(c_704, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_636, c_583])).
% 3.42/1.54  tff(c_68, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.42/1.54  tff(c_164, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_68, c_157])).
% 3.42/1.54  tff(c_568, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_164, c_559])).
% 3.42/1.54  tff(c_705, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_704, c_568])).
% 3.42/1.54  tff(c_16, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.42/1.54  tff(c_775, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_705, c_16])).
% 3.42/1.54  tff(c_781, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_775])).
% 3.42/1.54  tff(c_1329, plain, (k1_enumset1('#skF_4', '#skF_5', '#skF_3')=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1323, c_781])).
% 3.42/1.54  tff(c_20, plain, (![E_21, A_15, B_16]: (r2_hidden(E_21, k1_enumset1(A_15, B_16, E_21)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.42/1.54  tff(c_1363, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1329, c_20])).
% 3.42/1.54  tff(c_1273, plain, (![E_138, C_139, B_140, A_141]: (E_138=C_139 | E_138=B_140 | E_138=A_141 | ~r2_hidden(E_138, k1_enumset1(A_141, B_140, C_139)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.42/1.54  tff(c_1517, plain, (![E_162, B_163, A_164]: (E_162=B_163 | E_162=A_164 | E_162=A_164 | ~r2_hidden(E_162, k2_tarski(A_164, B_163)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1273])).
% 3.42/1.54  tff(c_1520, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1363, c_1517])).
% 3.42/1.54  tff(c_1533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_66, c_64, c_1520])).
% 3.42/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.54  
% 3.42/1.54  Inference rules
% 3.42/1.54  ----------------------
% 3.42/1.54  #Ref     : 0
% 3.42/1.54  #Sup     : 372
% 3.42/1.54  #Fact    : 0
% 3.42/1.54  #Define  : 0
% 3.42/1.54  #Split   : 0
% 3.42/1.54  #Chain   : 0
% 3.42/1.54  #Close   : 0
% 3.42/1.54  
% 3.42/1.54  Ordering : KBO
% 3.42/1.54  
% 3.42/1.54  Simplification rules
% 3.42/1.54  ----------------------
% 3.42/1.54  #Subsume      : 50
% 3.42/1.54  #Demod        : 183
% 3.42/1.54  #Tautology    : 259
% 3.42/1.54  #SimpNegUnit  : 1
% 3.42/1.54  #BackRed      : 1
% 3.42/1.54  
% 3.42/1.54  #Partial instantiations: 0
% 3.42/1.54  #Strategies tried      : 1
% 3.42/1.54  
% 3.42/1.54  Timing (in seconds)
% 3.42/1.54  ----------------------
% 3.42/1.54  Preprocessing        : 0.34
% 3.42/1.54  Parsing              : 0.18
% 3.42/1.54  CNF conversion       : 0.02
% 3.42/1.54  Main loop            : 0.43
% 3.42/1.54  Inferencing          : 0.14
% 3.42/1.54  Reduction            : 0.17
% 3.42/1.54  Demodulation         : 0.14
% 3.42/1.54  BG Simplification    : 0.02
% 3.42/1.54  Subsumption          : 0.07
% 3.42/1.54  Abstraction          : 0.02
% 3.42/1.54  MUC search           : 0.00
% 3.42/1.54  Cooper               : 0.00
% 3.42/1.54  Total                : 0.80
% 3.42/1.54  Index Insertion      : 0.00
% 3.42/1.54  Index Deletion       : 0.00
% 3.42/1.54  Index Matching       : 0.00
% 3.42/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
