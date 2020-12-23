%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:29 EST 2020

% Result     : Theorem 9.27s
% Output     : CNFRefutation 9.69s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 203 expanded)
%              Number of leaves         :   36 (  87 expanded)
%              Depth                    :   11
%              Number of atoms          :   66 ( 197 expanded)
%              Number of equality atoms :   43 ( 170 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_68,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_610,plain,(
    ! [A_141,B_142] : k5_xboole_0(k5_xboole_0(A_141,B_142),k2_xboole_0(A_141,B_142)) = k3_xboole_0(A_141,B_142) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_668,plain,(
    ! [A_8] : k5_xboole_0(k5_xboole_0(A_8,A_8),A_8) = k3_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_610])).

tff(c_674,plain,(
    ! [A_8] : k5_xboole_0(k1_xboole_0,A_8) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16,c_668])).

tff(c_372,plain,(
    ! [A_130,B_131,C_132] : k5_xboole_0(k5_xboole_0(A_130,B_131),C_132) = k5_xboole_0(A_130,k5_xboole_0(B_131,C_132)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_411,plain,(
    ! [A_15,C_132] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_132)) = k5_xboole_0(k1_xboole_0,C_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_372])).

tff(c_836,plain,(
    ! [A_15,C_132] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_132)) = C_132 ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_411])).

tff(c_678,plain,(
    ! [A_143] : k5_xboole_0(k1_xboole_0,A_143) = A_143 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16,c_668])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_709,plain,(
    ! [A_143] : k5_xboole_0(A_143,k1_xboole_0) = A_143 ),
    inference(superposition,[status(thm),theory(equality)],[c_678,c_2])).

tff(c_388,plain,(
    ! [A_130,B_131] : k5_xboole_0(A_130,k5_xboole_0(B_131,k5_xboole_0(A_130,B_131))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_16])).

tff(c_837,plain,(
    ! [A_149,C_150] : k5_xboole_0(A_149,k5_xboole_0(A_149,C_150)) = C_150 ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_411])).

tff(c_890,plain,(
    ! [B_131,A_130] : k5_xboole_0(B_131,k5_xboole_0(A_130,B_131)) = k5_xboole_0(A_130,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_837])).

tff(c_954,plain,(
    ! [B_155,A_156] : k5_xboole_0(B_155,k5_xboole_0(A_156,B_155)) = A_156 ),
    inference(demodulation,[status(thm),theory(equality)],[c_709,c_890])).

tff(c_990,plain,(
    ! [A_15,C_132] : k5_xboole_0(k5_xboole_0(A_15,C_132),C_132) = A_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_954])).

tff(c_70,plain,(
    k3_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k5_xboole_0(k5_xboole_0(A_12,B_13),C_14) = k5_xboole_0(A_12,k5_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16215,plain,(
    ! [A_21978,B_21979,C_21980] : k5_xboole_0(k5_xboole_0(A_21978,B_21979),k5_xboole_0(k2_xboole_0(A_21978,B_21979),C_21980)) = k5_xboole_0(k3_xboole_0(A_21978,B_21979),C_21980) ),
    inference(superposition,[status(thm),theory(equality)],[c_610,c_14])).

tff(c_16655,plain,(
    ! [A_21978,B_21979] : k5_xboole_0(k3_xboole_0(A_21978,B_21979),k2_xboole_0(A_21978,B_21979)) = k5_xboole_0(k5_xboole_0(A_21978,B_21979),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_16215])).

tff(c_17319,plain,(
    ! [A_22302,B_22303] : k5_xboole_0(k3_xboole_0(A_22302,B_22303),k2_xboole_0(A_22302,B_22303)) = k5_xboole_0(A_22302,B_22303) ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_2,c_16655])).

tff(c_17450,plain,(
    k5_xboole_0(k2_tarski('#skF_4','#skF_5'),k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) = k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_17319])).

tff(c_17477,plain,(
    k5_xboole_0(k2_tarski('#skF_4','#skF_5'),k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) = k5_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_17450])).

tff(c_924,plain,(
    ! [B_131,A_130] : k5_xboole_0(B_131,k5_xboole_0(A_130,B_131)) = A_130 ),
    inference(demodulation,[status(thm),theory(equality)],[c_709,c_890])).

tff(c_957,plain,(
    ! [A_156,B_155] : k5_xboole_0(k5_xboole_0(A_156,B_155),A_156) = B_155 ),
    inference(superposition,[status(thm),theory(equality)],[c_954,c_924])).

tff(c_18519,plain,(
    k5_xboole_0(k5_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')),k2_tarski('#skF_4','#skF_5')) = k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_17477,c_957])).

tff(c_18552,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_990,c_18519])).

tff(c_66,plain,(
    ! [A_74,B_75] : k3_tarski(k2_tarski(A_74,B_75)) = k2_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_145,plain,(
    ! [A_91,B_92] : k1_enumset1(A_91,A_91,B_92) = k2_tarski(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    ! [E_24,B_19,C_20] : r2_hidden(E_24,k1_enumset1(E_24,B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_151,plain,(
    ! [A_91,B_92] : r2_hidden(A_91,k2_tarski(A_91,B_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_26])).

tff(c_64,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(A_72,k3_tarski(B_73))
      | ~ r2_hidden(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_231,plain,(
    ! [C_113,B_114,A_115] :
      ( r2_hidden(C_113,B_114)
      | ~ r2_hidden(C_113,A_115)
      | ~ r1_tarski(A_115,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_323,plain,(
    ! [A_125,B_126,B_127] :
      ( r2_hidden(A_125,B_126)
      | ~ r1_tarski(k2_tarski(A_125,B_127),B_126) ) ),
    inference(resolution,[status(thm)],[c_151,c_231])).

tff(c_5796,plain,(
    ! [A_12580,B_12581,B_12582] :
      ( r2_hidden(A_12580,k3_tarski(B_12581))
      | ~ r2_hidden(k2_tarski(A_12580,B_12582),B_12581) ) ),
    inference(resolution,[status(thm)],[c_64,c_323])).

tff(c_5839,plain,(
    ! [A_12580,B_12582,B_92] : r2_hidden(A_12580,k3_tarski(k2_tarski(k2_tarski(A_12580,B_12582),B_92))) ),
    inference(resolution,[status(thm)],[c_151,c_5796])).

tff(c_5867,plain,(
    ! [A_12580,B_12582,B_92] : r2_hidden(A_12580,k2_xboole_0(k2_tarski(A_12580,B_12582),B_92)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5839])).

tff(c_18588,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_18552,c_5867])).

tff(c_18608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_18588])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:06:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.27/3.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.61/3.89  
% 9.61/3.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.63/3.89  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 9.63/3.89  
% 9.63/3.89  %Foreground sorts:
% 9.63/3.89  
% 9.63/3.89  
% 9.63/3.89  %Background operators:
% 9.63/3.89  
% 9.63/3.89  
% 9.63/3.89  %Foreground operators:
% 9.63/3.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.63/3.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.63/3.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.63/3.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.63/3.89  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.63/3.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.63/3.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.63/3.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.63/3.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.63/3.89  tff('#skF_5', type, '#skF_5': $i).
% 9.63/3.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.63/3.89  tff('#skF_6', type, '#skF_6': $i).
% 9.63/3.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.63/3.89  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.63/3.89  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.63/3.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.63/3.89  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.63/3.89  tff('#skF_4', type, '#skF_4': $i).
% 9.63/3.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.63/3.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.63/3.89  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 9.63/3.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.63/3.89  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.63/3.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.63/3.89  
% 9.69/3.90  tff(f_90, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 9.69/3.90  tff(f_38, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 9.69/3.90  tff(f_42, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 9.69/3.90  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 9.69/3.90  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 9.69/3.90  tff(f_40, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.69/3.90  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 9.69/3.90  tff(f_85, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 9.69/3.90  tff(f_69, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 9.69/3.90  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 9.69/3.90  tff(f_83, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 9.69/3.90  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.69/3.90  tff(c_68, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.69/3.90  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.69/3.90  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.69/3.90  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.69/3.90  tff(c_610, plain, (![A_141, B_142]: (k5_xboole_0(k5_xboole_0(A_141, B_142), k2_xboole_0(A_141, B_142))=k3_xboole_0(A_141, B_142))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.69/3.90  tff(c_668, plain, (![A_8]: (k5_xboole_0(k5_xboole_0(A_8, A_8), A_8)=k3_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_610])).
% 9.69/3.90  tff(c_674, plain, (![A_8]: (k5_xboole_0(k1_xboole_0, A_8)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16, c_668])).
% 9.69/3.90  tff(c_372, plain, (![A_130, B_131, C_132]: (k5_xboole_0(k5_xboole_0(A_130, B_131), C_132)=k5_xboole_0(A_130, k5_xboole_0(B_131, C_132)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.69/3.90  tff(c_411, plain, (![A_15, C_132]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_132))=k5_xboole_0(k1_xboole_0, C_132))), inference(superposition, [status(thm), theory('equality')], [c_16, c_372])).
% 9.69/3.90  tff(c_836, plain, (![A_15, C_132]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_132))=C_132)), inference(demodulation, [status(thm), theory('equality')], [c_674, c_411])).
% 9.69/3.90  tff(c_678, plain, (![A_143]: (k5_xboole_0(k1_xboole_0, A_143)=A_143)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16, c_668])).
% 9.69/3.90  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.69/3.90  tff(c_709, plain, (![A_143]: (k5_xboole_0(A_143, k1_xboole_0)=A_143)), inference(superposition, [status(thm), theory('equality')], [c_678, c_2])).
% 9.69/3.90  tff(c_388, plain, (![A_130, B_131]: (k5_xboole_0(A_130, k5_xboole_0(B_131, k5_xboole_0(A_130, B_131)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_372, c_16])).
% 9.69/3.90  tff(c_837, plain, (![A_149, C_150]: (k5_xboole_0(A_149, k5_xboole_0(A_149, C_150))=C_150)), inference(demodulation, [status(thm), theory('equality')], [c_674, c_411])).
% 9.69/3.90  tff(c_890, plain, (![B_131, A_130]: (k5_xboole_0(B_131, k5_xboole_0(A_130, B_131))=k5_xboole_0(A_130, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_388, c_837])).
% 9.69/3.90  tff(c_954, plain, (![B_155, A_156]: (k5_xboole_0(B_155, k5_xboole_0(A_156, B_155))=A_156)), inference(demodulation, [status(thm), theory('equality')], [c_709, c_890])).
% 9.69/3.90  tff(c_990, plain, (![A_15, C_132]: (k5_xboole_0(k5_xboole_0(A_15, C_132), C_132)=A_15)), inference(superposition, [status(thm), theory('equality')], [c_836, c_954])).
% 9.69/3.90  tff(c_70, plain, (k3_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.69/3.90  tff(c_14, plain, (![A_12, B_13, C_14]: (k5_xboole_0(k5_xboole_0(A_12, B_13), C_14)=k5_xboole_0(A_12, k5_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.69/3.90  tff(c_16215, plain, (![A_21978, B_21979, C_21980]: (k5_xboole_0(k5_xboole_0(A_21978, B_21979), k5_xboole_0(k2_xboole_0(A_21978, B_21979), C_21980))=k5_xboole_0(k3_xboole_0(A_21978, B_21979), C_21980))), inference(superposition, [status(thm), theory('equality')], [c_610, c_14])).
% 9.69/3.90  tff(c_16655, plain, (![A_21978, B_21979]: (k5_xboole_0(k3_xboole_0(A_21978, B_21979), k2_xboole_0(A_21978, B_21979))=k5_xboole_0(k5_xboole_0(A_21978, B_21979), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_16215])).
% 9.69/3.90  tff(c_17319, plain, (![A_22302, B_22303]: (k5_xboole_0(k3_xboole_0(A_22302, B_22303), k2_xboole_0(A_22302, B_22303))=k5_xboole_0(A_22302, B_22303))), inference(demodulation, [status(thm), theory('equality')], [c_674, c_2, c_16655])).
% 9.69/3.90  tff(c_17450, plain, (k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))=k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_70, c_17319])).
% 9.69/3.90  tff(c_17477, plain, (k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))=k5_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_17450])).
% 9.69/3.90  tff(c_924, plain, (![B_131, A_130]: (k5_xboole_0(B_131, k5_xboole_0(A_130, B_131))=A_130)), inference(demodulation, [status(thm), theory('equality')], [c_709, c_890])).
% 9.69/3.90  tff(c_957, plain, (![A_156, B_155]: (k5_xboole_0(k5_xboole_0(A_156, B_155), A_156)=B_155)), inference(superposition, [status(thm), theory('equality')], [c_954, c_924])).
% 9.69/3.90  tff(c_18519, plain, (k5_xboole_0(k5_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')), k2_tarski('#skF_4', '#skF_5'))=k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_17477, c_957])).
% 9.69/3.90  tff(c_18552, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_990, c_18519])).
% 9.69/3.90  tff(c_66, plain, (![A_74, B_75]: (k3_tarski(k2_tarski(A_74, B_75))=k2_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.69/3.90  tff(c_145, plain, (![A_91, B_92]: (k1_enumset1(A_91, A_91, B_92)=k2_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.69/3.90  tff(c_26, plain, (![E_24, B_19, C_20]: (r2_hidden(E_24, k1_enumset1(E_24, B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.69/3.90  tff(c_151, plain, (![A_91, B_92]: (r2_hidden(A_91, k2_tarski(A_91, B_92)))), inference(superposition, [status(thm), theory('equality')], [c_145, c_26])).
% 9.69/3.90  tff(c_64, plain, (![A_72, B_73]: (r1_tarski(A_72, k3_tarski(B_73)) | ~r2_hidden(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.69/3.90  tff(c_231, plain, (![C_113, B_114, A_115]: (r2_hidden(C_113, B_114) | ~r2_hidden(C_113, A_115) | ~r1_tarski(A_115, B_114))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.69/3.90  tff(c_323, plain, (![A_125, B_126, B_127]: (r2_hidden(A_125, B_126) | ~r1_tarski(k2_tarski(A_125, B_127), B_126))), inference(resolution, [status(thm)], [c_151, c_231])).
% 9.69/3.90  tff(c_5796, plain, (![A_12580, B_12581, B_12582]: (r2_hidden(A_12580, k3_tarski(B_12581)) | ~r2_hidden(k2_tarski(A_12580, B_12582), B_12581))), inference(resolution, [status(thm)], [c_64, c_323])).
% 9.69/3.90  tff(c_5839, plain, (![A_12580, B_12582, B_92]: (r2_hidden(A_12580, k3_tarski(k2_tarski(k2_tarski(A_12580, B_12582), B_92))))), inference(resolution, [status(thm)], [c_151, c_5796])).
% 9.69/3.90  tff(c_5867, plain, (![A_12580, B_12582, B_92]: (r2_hidden(A_12580, k2_xboole_0(k2_tarski(A_12580, B_12582), B_92)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5839])).
% 9.69/3.90  tff(c_18588, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_18552, c_5867])).
% 9.69/3.90  tff(c_18608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_18588])).
% 9.69/3.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.69/3.90  
% 9.69/3.90  Inference rules
% 9.69/3.90  ----------------------
% 9.69/3.90  #Ref     : 0
% 9.69/3.90  #Sup     : 3593
% 9.69/3.90  #Fact    : 18
% 9.69/3.90  #Define  : 0
% 9.69/3.90  #Split   : 0
% 9.69/3.90  #Chain   : 0
% 9.69/3.90  #Close   : 0
% 9.69/3.90  
% 9.69/3.90  Ordering : KBO
% 9.69/3.90  
% 9.69/3.90  Simplification rules
% 9.69/3.90  ----------------------
% 9.69/3.90  #Subsume      : 264
% 9.69/3.90  #Demod        : 2707
% 9.69/3.90  #Tautology    : 1138
% 9.69/3.90  #SimpNegUnit  : 1
% 9.69/3.90  #BackRed      : 5
% 9.69/3.90  
% 9.69/3.90  #Partial instantiations: 8322
% 9.69/3.90  #Strategies tried      : 1
% 9.69/3.90  
% 9.69/3.90  Timing (in seconds)
% 9.69/3.90  ----------------------
% 9.69/3.91  Preprocessing        : 0.36
% 9.69/3.91  Parsing              : 0.19
% 9.69/3.91  CNF conversion       : 0.03
% 9.69/3.91  Main loop            : 2.74
% 9.69/3.91  Inferencing          : 0.89
% 9.69/3.91  Reduction            : 1.32
% 9.69/3.91  Demodulation         : 1.20
% 9.69/3.91  BG Simplification    : 0.09
% 9.69/3.91  Subsumption          : 0.33
% 9.69/3.91  Abstraction          : 0.11
% 9.69/3.91  MUC search           : 0.00
% 9.69/3.91  Cooper               : 0.00
% 9.69/3.91  Total                : 3.13
% 9.69/3.91  Index Insertion      : 0.00
% 9.69/3.91  Index Deletion       : 0.00
% 9.69/3.91  Index Matching       : 0.00
% 9.73/3.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
