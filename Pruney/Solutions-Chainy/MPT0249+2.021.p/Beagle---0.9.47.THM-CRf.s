%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:26 EST 2020

% Result     : Theorem 4.50s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 158 expanded)
%              Number of leaves         :   38 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :   86 ( 222 expanded)
%              Number of equality atoms :   58 ( 174 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_58,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_60,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_101,plain,(
    ! [A_64,B_65] : r1_tarski(A_64,k2_xboole_0(A_64,B_65)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_104,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_101])).

tff(c_320,plain,(
    ! [B_107,A_108] :
      ( k1_tarski(B_107) = A_108
      | k1_xboole_0 = A_108
      | ~ r1_tarski(A_108,k1_tarski(B_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_323,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_104,c_320])).

tff(c_333,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_323])).

tff(c_340,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_60])).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_219,plain,(
    ! [A_81,B_82] :
      ( r1_xboole_0(k1_tarski(A_81),B_82)
      | r2_hidden(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1629,plain,(
    ! [A_166,B_167] :
      ( k4_xboole_0(k1_tarski(A_166),B_167) = k1_tarski(A_166)
      | r2_hidden(A_166,B_167) ) ),
    inference(resolution,[status(thm)],[c_219,c_14])).

tff(c_1642,plain,(
    ! [B_167] :
      ( k4_xboole_0('#skF_2',B_167) = k1_tarski('#skF_1')
      | r2_hidden('#skF_1',B_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_1629])).

tff(c_1650,plain,(
    ! [B_167] :
      ( k4_xboole_0('#skF_2',B_167) = '#skF_2'
      | r2_hidden('#skF_1',B_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_1642])).

tff(c_24,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1038,plain,(
    ! [A_132,B_133,C_134] :
      ( r1_tarski(k2_tarski(A_132,B_133),C_134)
      | ~ r2_hidden(B_133,C_134)
      | ~ r2_hidden(A_132,C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2039,plain,(
    ! [A_179,C_180] :
      ( r1_tarski(k1_tarski(A_179),C_180)
      | ~ r2_hidden(A_179,C_180)
      | ~ r2_hidden(A_179,C_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1038])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2061,plain,(
    ! [A_181,C_182] :
      ( k2_xboole_0(k1_tarski(A_181),C_182) = C_182
      | ~ r2_hidden(A_181,C_182) ) ),
    inference(resolution,[status(thm)],[c_2039,c_10])).

tff(c_2201,plain,(
    ! [C_186] :
      ( k2_xboole_0('#skF_2',C_186) = C_186
      | ~ r2_hidden('#skF_1',C_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_2061])).

tff(c_3357,plain,(
    ! [B_217] :
      ( k2_xboole_0('#skF_2',B_217) = B_217
      | k4_xboole_0('#skF_2',B_217) = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_1650,c_2201])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_490,plain,(
    ! [A_118,B_119] : k5_xboole_0(k5_xboole_0(A_118,B_119),k2_xboole_0(A_118,B_119)) = k3_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_517,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_3'),'#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_490])).

tff(c_545,plain,(
    k5_xboole_0('#skF_2',k5_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_517])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_538,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k3_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_490])).

tff(c_546,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20,c_538])).

tff(c_645,plain,(
    ! [A_122,B_123,C_124] : k5_xboole_0(k5_xboole_0(A_122,B_123),C_124) = k5_xboole_0(A_122,k5_xboole_0(B_123,C_124)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_722,plain,(
    ! [A_18,C_124] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_124)) = k5_xboole_0(k1_xboole_0,C_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_645])).

tff(c_735,plain,(
    ! [A_18,C_124] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_124)) = C_124 ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_722])).

tff(c_830,plain,(
    k5_xboole_0('#skF_2',k3_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_735])).

tff(c_839,plain,(
    k5_xboole_0('#skF_3','#skF_2') = k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_830])).

tff(c_737,plain,(
    ! [A_125,C_126] : k5_xboole_0(A_125,k5_xboole_0(A_125,C_126)) = C_126 ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_722])).

tff(c_789,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_737])).

tff(c_1245,plain,(
    k5_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_839,c_789])).

tff(c_3388,plain,
    ( k5_xboole_0('#skF_2','#skF_2') = '#skF_3'
    | k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_3357,c_1245])).

tff(c_3431,plain,
    ( k1_xboole_0 = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_20,c_3388])).

tff(c_3433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_54,c_3431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:10:20 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.50/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.84  
% 4.50/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.84  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.50/1.84  
% 4.50/1.84  %Foreground sorts:
% 4.50/1.84  
% 4.50/1.84  
% 4.50/1.84  %Background operators:
% 4.50/1.84  
% 4.50/1.84  
% 4.50/1.84  %Foreground operators:
% 4.50/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.50/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.50/1.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.50/1.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.50/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.50/1.84  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.50/1.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.50/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.50/1.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.50/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.50/1.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.50/1.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.50/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.50/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.50/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.50/1.84  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.50/1.84  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.50/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.50/1.84  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.50/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.50/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.50/1.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.50/1.84  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.50/1.84  
% 4.50/1.86  tff(f_95, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 4.50/1.86  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.50/1.86  tff(f_74, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.50/1.86  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.50/1.86  tff(f_68, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.50/1.86  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.50/1.86  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.50/1.86  tff(f_82, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.50/1.86  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.50/1.86  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.50/1.86  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.50/1.86  tff(f_49, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 4.50/1.86  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.50/1.86  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.50/1.86  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.50/1.86  tff(c_58, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.50/1.86  tff(c_54, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.50/1.86  tff(c_56, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.50/1.86  tff(c_60, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.50/1.86  tff(c_101, plain, (![A_64, B_65]: (r1_tarski(A_64, k2_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.50/1.86  tff(c_104, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_101])).
% 4.50/1.86  tff(c_320, plain, (![B_107, A_108]: (k1_tarski(B_107)=A_108 | k1_xboole_0=A_108 | ~r1_tarski(A_108, k1_tarski(B_107)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.50/1.86  tff(c_323, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_104, c_320])).
% 4.50/1.86  tff(c_333, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_56, c_323])).
% 4.50/1.86  tff(c_340, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_333, c_60])).
% 4.50/1.86  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.50/1.86  tff(c_219, plain, (![A_81, B_82]: (r1_xboole_0(k1_tarski(A_81), B_82) | r2_hidden(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.50/1.86  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.50/1.86  tff(c_1629, plain, (![A_166, B_167]: (k4_xboole_0(k1_tarski(A_166), B_167)=k1_tarski(A_166) | r2_hidden(A_166, B_167))), inference(resolution, [status(thm)], [c_219, c_14])).
% 4.50/1.86  tff(c_1642, plain, (![B_167]: (k4_xboole_0('#skF_2', B_167)=k1_tarski('#skF_1') | r2_hidden('#skF_1', B_167))), inference(superposition, [status(thm), theory('equality')], [c_333, c_1629])).
% 4.50/1.86  tff(c_1650, plain, (![B_167]: (k4_xboole_0('#skF_2', B_167)='#skF_2' | r2_hidden('#skF_1', B_167))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_1642])).
% 4.50/1.86  tff(c_24, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.50/1.86  tff(c_1038, plain, (![A_132, B_133, C_134]: (r1_tarski(k2_tarski(A_132, B_133), C_134) | ~r2_hidden(B_133, C_134) | ~r2_hidden(A_132, C_134))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.50/1.86  tff(c_2039, plain, (![A_179, C_180]: (r1_tarski(k1_tarski(A_179), C_180) | ~r2_hidden(A_179, C_180) | ~r2_hidden(A_179, C_180))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1038])).
% 4.50/1.86  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.50/1.86  tff(c_2061, plain, (![A_181, C_182]: (k2_xboole_0(k1_tarski(A_181), C_182)=C_182 | ~r2_hidden(A_181, C_182))), inference(resolution, [status(thm)], [c_2039, c_10])).
% 4.50/1.86  tff(c_2201, plain, (![C_186]: (k2_xboole_0('#skF_2', C_186)=C_186 | ~r2_hidden('#skF_1', C_186))), inference(superposition, [status(thm), theory('equality')], [c_333, c_2061])).
% 4.50/1.86  tff(c_3357, plain, (![B_217]: (k2_xboole_0('#skF_2', B_217)=B_217 | k4_xboole_0('#skF_2', B_217)='#skF_2')), inference(resolution, [status(thm)], [c_1650, c_2201])).
% 4.50/1.86  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.50/1.86  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.50/1.86  tff(c_490, plain, (![A_118, B_119]: (k5_xboole_0(k5_xboole_0(A_118, B_119), k2_xboole_0(A_118, B_119))=k3_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.50/1.86  tff(c_517, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_3'), '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_340, c_490])).
% 4.50/1.86  tff(c_545, plain, (k5_xboole_0('#skF_2', k5_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_517])).
% 4.50/1.86  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.50/1.86  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.50/1.86  tff(c_538, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_490])).
% 4.50/1.86  tff(c_546, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_20, c_538])).
% 4.50/1.86  tff(c_645, plain, (![A_122, B_123, C_124]: (k5_xboole_0(k5_xboole_0(A_122, B_123), C_124)=k5_xboole_0(A_122, k5_xboole_0(B_123, C_124)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.50/1.86  tff(c_722, plain, (![A_18, C_124]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_124))=k5_xboole_0(k1_xboole_0, C_124))), inference(superposition, [status(thm), theory('equality')], [c_20, c_645])).
% 4.50/1.86  tff(c_735, plain, (![A_18, C_124]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_124))=C_124)), inference(demodulation, [status(thm), theory('equality')], [c_546, c_722])).
% 4.50/1.86  tff(c_830, plain, (k5_xboole_0('#skF_2', k3_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_545, c_735])).
% 4.50/1.86  tff(c_839, plain, (k5_xboole_0('#skF_3', '#skF_2')=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_830])).
% 4.50/1.86  tff(c_737, plain, (![A_125, C_126]: (k5_xboole_0(A_125, k5_xboole_0(A_125, C_126))=C_126)), inference(demodulation, [status(thm), theory('equality')], [c_546, c_722])).
% 4.50/1.86  tff(c_789, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_737])).
% 4.50/1.86  tff(c_1245, plain, (k5_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_839, c_789])).
% 4.50/1.86  tff(c_3388, plain, (k5_xboole_0('#skF_2', '#skF_2')='#skF_3' | k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_3357, c_1245])).
% 4.50/1.86  tff(c_3431, plain, (k1_xboole_0='#skF_3' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_340, c_20, c_3388])).
% 4.50/1.86  tff(c_3433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_54, c_3431])).
% 4.50/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.86  
% 4.50/1.86  Inference rules
% 4.50/1.86  ----------------------
% 4.50/1.86  #Ref     : 0
% 4.50/1.86  #Sup     : 841
% 4.50/1.86  #Fact    : 0
% 4.50/1.86  #Define  : 0
% 4.50/1.86  #Split   : 0
% 4.50/1.86  #Chain   : 0
% 4.50/1.86  #Close   : 0
% 4.50/1.86  
% 4.50/1.86  Ordering : KBO
% 4.50/1.86  
% 4.50/1.86  Simplification rules
% 4.50/1.86  ----------------------
% 4.50/1.86  #Subsume      : 27
% 4.50/1.86  #Demod        : 598
% 4.50/1.86  #Tautology    : 510
% 4.50/1.86  #SimpNegUnit  : 20
% 4.50/1.86  #BackRed      : 4
% 4.50/1.86  
% 4.50/1.86  #Partial instantiations: 0
% 4.50/1.86  #Strategies tried      : 1
% 4.50/1.86  
% 4.50/1.86  Timing (in seconds)
% 4.50/1.86  ----------------------
% 4.50/1.86  Preprocessing        : 0.35
% 4.50/1.86  Parsing              : 0.19
% 4.50/1.86  CNF conversion       : 0.02
% 4.50/1.86  Main loop            : 0.71
% 4.50/1.86  Inferencing          : 0.23
% 4.50/1.86  Reduction            : 0.30
% 4.50/1.86  Demodulation         : 0.25
% 4.50/1.86  BG Simplification    : 0.03
% 4.50/1.86  Subsumption          : 0.10
% 4.50/1.86  Abstraction          : 0.03
% 4.50/1.86  MUC search           : 0.00
% 4.50/1.86  Cooper               : 0.00
% 4.50/1.86  Total                : 1.09
% 4.50/1.86  Index Insertion      : 0.00
% 4.50/1.86  Index Deletion       : 0.00
% 4.50/1.86  Index Matching       : 0.00
% 4.50/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
