%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:27 EST 2020

% Result     : Theorem 5.64s
% Output     : CNFRefutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 152 expanded)
%              Number of leaves         :   36 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :   61 ( 140 expanded)
%              Number of equality atoms :   43 ( 121 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_42,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_44,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_77,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_62,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_393,plain,(
    ! [A_117,B_118,C_119] : k5_xboole_0(k5_xboole_0(A_117,B_118),C_119) = k5_xboole_0(A_117,k5_xboole_0(B_118,C_119)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_414,plain,(
    ! [A_117,B_118] : k5_xboole_0(A_117,k5_xboole_0(B_118,k5_xboole_0(A_117,B_118))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_18])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_359,plain,(
    ! [A_115,B_116] : k5_xboole_0(k5_xboole_0(A_115,B_116),k2_xboole_0(A_115,B_116)) = k3_xboole_0(A_115,B_116) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_380,plain,(
    ! [A_6] : k5_xboole_0(k5_xboole_0(A_6,A_6),A_6) = k3_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_359])).

tff(c_391,plain,(
    ! [A_6] : k5_xboole_0(k1_xboole_0,A_6) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_18,c_380])).

tff(c_436,plain,(
    ! [A_16,C_119] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_119)) = k5_xboole_0(k1_xboole_0,C_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_393])).

tff(c_617,plain,(
    ! [A_128,C_129] : k5_xboole_0(A_128,k5_xboole_0(A_128,C_129)) = C_129 ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_436])).

tff(c_657,plain,(
    ! [B_118,A_117] : k5_xboole_0(B_118,k5_xboole_0(A_117,B_118)) = k5_xboole_0(A_117,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_617])).

tff(c_698,plain,(
    ! [B_118,A_117] : k5_xboole_0(B_118,k5_xboole_0(A_117,B_118)) = A_117 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_657])).

tff(c_707,plain,(
    ! [B_130,A_131] : k5_xboole_0(B_130,k5_xboole_0(A_131,B_130)) = A_131 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_657])).

tff(c_710,plain,(
    ! [A_131,B_130] : k5_xboole_0(k5_xboole_0(A_131,B_130),A_131) = B_130 ),
    inference(superposition,[status(thm),theory(equality)],[c_707,c_698])).

tff(c_22,plain,(
    ! [B_20,A_19] : k2_tarski(B_20,A_19) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_192,plain,(
    ! [A_81,B_82] : k3_tarski(k2_tarski(A_81,B_82)) = k2_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_211,plain,(
    ! [B_85,A_86] : k3_tarski(k2_tarski(B_85,A_86)) = k2_xboole_0(A_86,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_192])).

tff(c_60,plain,(
    ! [A_55,B_56] : k3_tarski(k2_tarski(A_55,B_56)) = k2_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_217,plain,(
    ! [B_85,A_86] : k2_xboole_0(B_85,A_86) = k2_xboole_0(A_86,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_60])).

tff(c_64,plain,(
    k3_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    ! [A_17,B_18] : k5_xboole_0(k5_xboole_0(A_17,B_18),k2_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_5907,plain,(
    ! [A_12770,B_12771] : k5_xboole_0(k5_xboole_0(A_12770,B_12771),k3_xboole_0(A_12770,B_12771)) = k2_xboole_0(A_12770,B_12771) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_617])).

tff(c_6082,plain,(
    k5_xboole_0(k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),k2_tarski('#skF_4','#skF_5')) = k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_5907])).

tff(c_6116,plain,(
    k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_710,c_217,c_6082])).

tff(c_406,plain,(
    ! [A_117,B_118] : k5_xboole_0(A_117,k5_xboole_0(B_118,k2_xboole_0(A_117,B_118))) = k3_xboole_0(A_117,B_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_20])).

tff(c_6123,plain,(
    k5_xboole_0('#skF_6',k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) = k3_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6116,c_406])).

tff(c_6132,plain,(
    k3_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_6123])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6141,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6132,c_12])).

tff(c_158,plain,(
    ! [A_75,B_76] : k1_enumset1(A_75,A_75,B_76) = k2_tarski(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    ! [E_27,A_21,C_23] : r2_hidden(E_27,k1_enumset1(A_21,E_27,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_164,plain,(
    ! [A_75,B_76] : r2_hidden(A_75,k2_tarski(A_75,B_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_28])).

tff(c_275,plain,(
    ! [C_91,B_92,A_93] :
      ( r2_hidden(C_91,B_92)
      | ~ r2_hidden(C_91,A_93)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_290,plain,(
    ! [A_75,B_92,B_76] :
      ( r2_hidden(A_75,B_92)
      | ~ r1_tarski(k2_tarski(A_75,B_76),B_92) ) ),
    inference(resolution,[status(thm)],[c_164,c_275])).

tff(c_6151,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_6141,c_290])).

tff(c_6158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_6151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.64/2.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.64/2.13  
% 5.64/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.64/2.13  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 5.64/2.13  
% 5.64/2.13  %Foreground sorts:
% 5.64/2.13  
% 5.64/2.13  
% 5.64/2.13  %Background operators:
% 5.64/2.13  
% 5.64/2.13  
% 5.64/2.13  %Foreground operators:
% 5.64/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.64/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.64/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.64/2.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.64/2.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.64/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.64/2.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.64/2.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.64/2.13  tff('#skF_5', type, '#skF_5': $i).
% 5.64/2.13  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.64/2.13  tff('#skF_6', type, '#skF_6': $i).
% 5.64/2.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.64/2.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.64/2.13  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.64/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.64/2.13  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.64/2.13  tff('#skF_4', type, '#skF_4': $i).
% 5.64/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.64/2.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.64/2.13  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.64/2.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.64/2.13  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.64/2.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.64/2.13  
% 5.71/2.15  tff(f_82, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 5.71/2.15  tff(f_40, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.71/2.15  tff(f_42, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.71/2.15  tff(f_44, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.71/2.15  tff(f_36, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.71/2.15  tff(f_34, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 5.71/2.15  tff(f_46, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 5.71/2.15  tff(f_48, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.71/2.15  tff(f_77, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.71/2.15  tff(f_38, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.71/2.15  tff(f_65, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.71/2.15  tff(f_63, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.71/2.15  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.71/2.15  tff(c_62, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.71/2.15  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.71/2.15  tff(c_393, plain, (![A_117, B_118, C_119]: (k5_xboole_0(k5_xboole_0(A_117, B_118), C_119)=k5_xboole_0(A_117, k5_xboole_0(B_118, C_119)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.71/2.15  tff(c_18, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.71/2.15  tff(c_414, plain, (![A_117, B_118]: (k5_xboole_0(A_117, k5_xboole_0(B_118, k5_xboole_0(A_117, B_118)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_393, c_18])).
% 5.71/2.15  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.71/2.15  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.71/2.15  tff(c_359, plain, (![A_115, B_116]: (k5_xboole_0(k5_xboole_0(A_115, B_116), k2_xboole_0(A_115, B_116))=k3_xboole_0(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.71/2.15  tff(c_380, plain, (![A_6]: (k5_xboole_0(k5_xboole_0(A_6, A_6), A_6)=k3_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_359])).
% 5.71/2.15  tff(c_391, plain, (![A_6]: (k5_xboole_0(k1_xboole_0, A_6)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_18, c_380])).
% 5.71/2.15  tff(c_436, plain, (![A_16, C_119]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_119))=k5_xboole_0(k1_xboole_0, C_119))), inference(superposition, [status(thm), theory('equality')], [c_18, c_393])).
% 5.71/2.15  tff(c_617, plain, (![A_128, C_129]: (k5_xboole_0(A_128, k5_xboole_0(A_128, C_129))=C_129)), inference(demodulation, [status(thm), theory('equality')], [c_391, c_436])).
% 5.71/2.15  tff(c_657, plain, (![B_118, A_117]: (k5_xboole_0(B_118, k5_xboole_0(A_117, B_118))=k5_xboole_0(A_117, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_414, c_617])).
% 5.71/2.15  tff(c_698, plain, (![B_118, A_117]: (k5_xboole_0(B_118, k5_xboole_0(A_117, B_118))=A_117)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_657])).
% 5.71/2.15  tff(c_707, plain, (![B_130, A_131]: (k5_xboole_0(B_130, k5_xboole_0(A_131, B_130))=A_131)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_657])).
% 5.71/2.15  tff(c_710, plain, (![A_131, B_130]: (k5_xboole_0(k5_xboole_0(A_131, B_130), A_131)=B_130)), inference(superposition, [status(thm), theory('equality')], [c_707, c_698])).
% 5.71/2.15  tff(c_22, plain, (![B_20, A_19]: (k2_tarski(B_20, A_19)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.71/2.15  tff(c_192, plain, (![A_81, B_82]: (k3_tarski(k2_tarski(A_81, B_82))=k2_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.71/2.15  tff(c_211, plain, (![B_85, A_86]: (k3_tarski(k2_tarski(B_85, A_86))=k2_xboole_0(A_86, B_85))), inference(superposition, [status(thm), theory('equality')], [c_22, c_192])).
% 5.71/2.15  tff(c_60, plain, (![A_55, B_56]: (k3_tarski(k2_tarski(A_55, B_56))=k2_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.71/2.15  tff(c_217, plain, (![B_85, A_86]: (k2_xboole_0(B_85, A_86)=k2_xboole_0(A_86, B_85))), inference(superposition, [status(thm), theory('equality')], [c_211, c_60])).
% 5.71/2.15  tff(c_64, plain, (k3_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.71/2.15  tff(c_20, plain, (![A_17, B_18]: (k5_xboole_0(k5_xboole_0(A_17, B_18), k2_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.71/2.15  tff(c_5907, plain, (![A_12770, B_12771]: (k5_xboole_0(k5_xboole_0(A_12770, B_12771), k3_xboole_0(A_12770, B_12771))=k2_xboole_0(A_12770, B_12771))), inference(superposition, [status(thm), theory('equality')], [c_20, c_617])).
% 5.71/2.15  tff(c_6082, plain, (k5_xboole_0(k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), k2_tarski('#skF_4', '#skF_5'))=k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_64, c_5907])).
% 5.71/2.15  tff(c_6116, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_710, c_217, c_6082])).
% 5.71/2.15  tff(c_406, plain, (![A_117, B_118]: (k5_xboole_0(A_117, k5_xboole_0(B_118, k2_xboole_0(A_117, B_118)))=k3_xboole_0(A_117, B_118))), inference(superposition, [status(thm), theory('equality')], [c_393, c_20])).
% 5.71/2.15  tff(c_6123, plain, (k5_xboole_0('#skF_6', k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))=k3_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6116, c_406])).
% 5.71/2.15  tff(c_6132, plain, (k3_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_698, c_6123])).
% 5.71/2.15  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.71/2.15  tff(c_6141, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6132, c_12])).
% 5.71/2.15  tff(c_158, plain, (![A_75, B_76]: (k1_enumset1(A_75, A_75, B_76)=k2_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.71/2.15  tff(c_28, plain, (![E_27, A_21, C_23]: (r2_hidden(E_27, k1_enumset1(A_21, E_27, C_23)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.71/2.15  tff(c_164, plain, (![A_75, B_76]: (r2_hidden(A_75, k2_tarski(A_75, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_158, c_28])).
% 5.71/2.15  tff(c_275, plain, (![C_91, B_92, A_93]: (r2_hidden(C_91, B_92) | ~r2_hidden(C_91, A_93) | ~r1_tarski(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.71/2.15  tff(c_290, plain, (![A_75, B_92, B_76]: (r2_hidden(A_75, B_92) | ~r1_tarski(k2_tarski(A_75, B_76), B_92))), inference(resolution, [status(thm)], [c_164, c_275])).
% 5.71/2.15  tff(c_6151, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_6141, c_290])).
% 5.71/2.15  tff(c_6158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_6151])).
% 5.71/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.71/2.15  
% 5.71/2.15  Inference rules
% 5.71/2.15  ----------------------
% 5.71/2.15  #Ref     : 0
% 5.71/2.15  #Sup     : 1101
% 5.71/2.15  #Fact    : 18
% 5.71/2.15  #Define  : 0
% 5.71/2.15  #Split   : 0
% 5.71/2.15  #Chain   : 0
% 5.71/2.15  #Close   : 0
% 5.71/2.15  
% 5.71/2.15  Ordering : KBO
% 5.71/2.15  
% 5.71/2.15  Simplification rules
% 5.71/2.15  ----------------------
% 5.71/2.15  #Subsume      : 104
% 5.71/2.15  #Demod        : 591
% 5.71/2.15  #Tautology    : 574
% 5.71/2.15  #SimpNegUnit  : 1
% 5.71/2.15  #BackRed      : 1
% 5.71/2.15  
% 5.71/2.15  #Partial instantiations: 4536
% 5.71/2.15  #Strategies tried      : 1
% 5.71/2.15  
% 5.71/2.15  Timing (in seconds)
% 5.71/2.15  ----------------------
% 5.71/2.16  Preprocessing        : 0.35
% 5.71/2.16  Parsing              : 0.19
% 5.71/2.16  CNF conversion       : 0.03
% 5.71/2.16  Main loop            : 1.00
% 5.71/2.16  Inferencing          : 0.48
% 5.71/2.16  Reduction            : 0.31
% 5.71/2.16  Demodulation         : 0.25
% 5.71/2.16  BG Simplification    : 0.04
% 5.71/2.16  Subsumption          : 0.12
% 5.71/2.16  Abstraction          : 0.05
% 5.71/2.16  MUC search           : 0.00
% 5.71/2.16  Cooper               : 0.00
% 5.71/2.16  Total                : 1.39
% 5.71/2.16  Index Insertion      : 0.00
% 5.71/2.16  Index Deletion       : 0.00
% 5.71/2.16  Index Matching       : 0.00
% 5.71/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
