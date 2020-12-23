%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:36 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.83s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 156 expanded)
%              Number of leaves         :   28 (  63 expanded)
%              Depth                    :   16
%              Number of atoms          :   85 ( 198 expanded)
%              Number of equality atoms :   45 ( 100 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_57,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_61,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(c_32,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [B_21,A_20] : k2_tarski(B_21,A_20) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_120,plain,(
    ! [A_37,B_38] : k1_setfam_1(k2_tarski(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_144,plain,(
    ! [B_41,A_42] : k1_setfam_1(k2_tarski(B_41,A_42)) = k3_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_120])).

tff(c_28,plain,(
    ! [A_24,B_25] : k1_setfam_1(k2_tarski(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_150,plain,(
    ! [B_41,A_42] : k3_xboole_0(B_41,A_42) = k3_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_28])).

tff(c_201,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_210,plain,(
    ! [A_45,B_46] : r1_tarski(k3_xboole_0(A_45,B_46),A_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_14])).

tff(c_12,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_239,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_261,plain,(
    ! [A_53] :
      ( k1_xboole_0 = A_53
      | ~ r1_tarski(A_53,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_239])).

tff(c_289,plain,(
    ! [B_54] : k3_xboole_0(k1_xboole_0,B_54) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_210,c_261])).

tff(c_309,plain,(
    ! [B_41] : k3_xboole_0(B_41,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_289])).

tff(c_219,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_201])).

tff(c_425,plain,(
    ! [A_61] : k4_xboole_0(A_61,A_61) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_219])).

tff(c_22,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_433,plain,(
    ! [A_61] : k4_xboole_0(A_61,k1_xboole_0) = k3_xboole_0(A_61,A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_22])).

tff(c_452,plain,(
    ! [A_61] : k3_xboole_0(A_61,A_61) = A_61 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_433])).

tff(c_34,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_981,plain,(
    ! [A_91,B_92,C_93] :
      ( r1_tarski(A_91,k2_xboole_0(B_92,C_93))
      | ~ r1_tarski(k4_xboole_0(A_91,B_92),C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1022,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(B_10,A_9)) ),
    inference(resolution,[status(thm)],[c_14,c_981])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_522,plain,(
    ! [A_65,B_66,C_67] :
      ( r1_tarski(k4_xboole_0(A_65,B_66),C_67)
      | ~ r1_tarski(A_65,k2_xboole_0(B_66,C_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1734,plain,(
    ! [A_140,C_141] :
      ( r1_tarski(A_140,C_141)
      | ~ r1_tarski(A_140,k2_xboole_0(k1_xboole_0,C_141)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_522])).

tff(c_1889,plain,(
    ! [C_142] : r1_tarski(k2_xboole_0(k1_xboole_0,C_142),C_142) ),
    inference(resolution,[status(thm)],[c_8,c_1734])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1914,plain,(
    ! [C_142] :
      ( k2_xboole_0(k1_xboole_0,C_142) = C_142
      | ~ r1_tarski(C_142,k2_xboole_0(k1_xboole_0,C_142)) ) ),
    inference(resolution,[status(thm)],[c_1889,c_4])).

tff(c_1994,plain,(
    ! [C_143] : k2_xboole_0(k1_xboole_0,C_143) = C_143 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_1914])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2046,plain,(
    ! [C_143] : k2_xboole_0(C_143,k1_xboole_0) = C_143 ),
    inference(superposition,[status(thm),theory(equality)],[c_1994,c_2])).

tff(c_3696,plain,(
    ! [A_212,B_213,C_214] :
      ( k4_xboole_0(A_212,B_213) = C_214
      | ~ r1_tarski(C_214,k4_xboole_0(A_212,B_213))
      | ~ r1_tarski(A_212,k2_xboole_0(B_213,C_214)) ) ),
    inference(resolution,[status(thm)],[c_522,c_4])).

tff(c_3769,plain,(
    ! [A_212,B_213] :
      ( k4_xboole_0(A_212,B_213) = k1_xboole_0
      | ~ r1_tarski(A_212,k2_xboole_0(B_213,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_12,c_3696])).

tff(c_3802,plain,(
    ! [A_215,B_216] :
      ( k4_xboole_0(A_215,B_216) = k1_xboole_0
      | ~ r1_tarski(A_215,B_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2046,c_3769])).

tff(c_3976,plain,(
    k4_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_3802])).

tff(c_4030,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3976,c_22])).

tff(c_4052,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_4030])).

tff(c_222,plain,(
    ! [A_47,B_48] : r1_tarski(k3_xboole_0(A_47,B_48),A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_14])).

tff(c_225,plain,(
    ! [B_41,A_42] : r1_tarski(k3_xboole_0(B_41,A_42),A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_222])).

tff(c_4651,plain,(
    ! [B_224,A_225] : k4_xboole_0(k3_xboole_0(B_224,A_225),A_225) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_225,c_3802])).

tff(c_4718,plain,(
    ! [B_224,A_225] : k4_xboole_0(k3_xboole_0(B_224,A_225),k1_xboole_0) = k3_xboole_0(k3_xboole_0(B_224,A_225),A_225) ),
    inference(superposition,[status(thm),theory(equality)],[c_4651,c_22])).

tff(c_13966,plain,(
    ! [B_347,A_348] : k3_xboole_0(k3_xboole_0(B_347,A_348),A_348) = k3_xboole_0(B_347,A_348) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_4718])).

tff(c_15811,plain,(
    ! [A_362,B_363] : k3_xboole_0(k3_xboole_0(A_362,B_363),A_362) = k3_xboole_0(B_363,A_362) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_13966])).

tff(c_16072,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k3_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4052,c_15811])).

tff(c_16149,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_16072])).

tff(c_30,plain,(
    ! [B_27,A_26] :
      ( k3_xboole_0(k1_relat_1(B_27),A_26) = k1_relat_1(k7_relat_1(B_27,A_26))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16530,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16149,c_30])).

tff(c_16606,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_16530])).

tff(c_16608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_16606])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:48:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.65/2.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.65/2.88  
% 7.65/2.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.65/2.89  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.65/2.89  
% 7.65/2.89  %Foreground sorts:
% 7.65/2.89  
% 7.65/2.89  
% 7.65/2.89  %Background operators:
% 7.65/2.89  
% 7.65/2.89  
% 7.65/2.89  %Foreground operators:
% 7.65/2.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.65/2.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.65/2.89  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.65/2.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.65/2.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.65/2.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.65/2.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.65/2.89  tff('#skF_2', type, '#skF_2': $i).
% 7.65/2.89  tff('#skF_1', type, '#skF_1': $i).
% 7.65/2.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.65/2.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.65/2.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.65/2.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.65/2.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.65/2.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.65/2.89  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.65/2.89  
% 7.83/2.90  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 7.83/2.90  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.83/2.90  tff(f_57, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.83/2.90  tff(f_61, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 7.83/2.90  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.83/2.90  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.83/2.90  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.83/2.90  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.83/2.90  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 7.83/2.90  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 7.83/2.90  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.83/2.90  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 7.83/2.90  tff(c_32, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.83/2.90  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.83/2.90  tff(c_16, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.83/2.90  tff(c_24, plain, (![B_21, A_20]: (k2_tarski(B_21, A_20)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.83/2.90  tff(c_120, plain, (![A_37, B_38]: (k1_setfam_1(k2_tarski(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.83/2.90  tff(c_144, plain, (![B_41, A_42]: (k1_setfam_1(k2_tarski(B_41, A_42))=k3_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_24, c_120])).
% 7.83/2.90  tff(c_28, plain, (![A_24, B_25]: (k1_setfam_1(k2_tarski(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.83/2.90  tff(c_150, plain, (![B_41, A_42]: (k3_xboole_0(B_41, A_42)=k3_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_144, c_28])).
% 7.83/2.90  tff(c_201, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.83/2.90  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.83/2.90  tff(c_210, plain, (![A_45, B_46]: (r1_tarski(k3_xboole_0(A_45, B_46), A_45))), inference(superposition, [status(thm), theory('equality')], [c_201, c_14])).
% 7.83/2.90  tff(c_12, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.83/2.90  tff(c_239, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.83/2.90  tff(c_261, plain, (![A_53]: (k1_xboole_0=A_53 | ~r1_tarski(A_53, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_239])).
% 7.83/2.90  tff(c_289, plain, (![B_54]: (k3_xboole_0(k1_xboole_0, B_54)=k1_xboole_0)), inference(resolution, [status(thm)], [c_210, c_261])).
% 7.83/2.90  tff(c_309, plain, (![B_41]: (k3_xboole_0(B_41, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_150, c_289])).
% 7.83/2.90  tff(c_219, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_201])).
% 7.83/2.90  tff(c_425, plain, (![A_61]: (k4_xboole_0(A_61, A_61)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_309, c_219])).
% 7.83/2.90  tff(c_22, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.83/2.90  tff(c_433, plain, (![A_61]: (k4_xboole_0(A_61, k1_xboole_0)=k3_xboole_0(A_61, A_61))), inference(superposition, [status(thm), theory('equality')], [c_425, c_22])).
% 7.83/2.90  tff(c_452, plain, (![A_61]: (k3_xboole_0(A_61, A_61)=A_61)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_433])).
% 7.83/2.90  tff(c_34, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.83/2.90  tff(c_981, plain, (![A_91, B_92, C_93]: (r1_tarski(A_91, k2_xboole_0(B_92, C_93)) | ~r1_tarski(k4_xboole_0(A_91, B_92), C_93))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.83/2.90  tff(c_1022, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(B_10, A_9)))), inference(resolution, [status(thm)], [c_14, c_981])).
% 7.83/2.90  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.83/2.90  tff(c_522, plain, (![A_65, B_66, C_67]: (r1_tarski(k4_xboole_0(A_65, B_66), C_67) | ~r1_tarski(A_65, k2_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.83/2.90  tff(c_1734, plain, (![A_140, C_141]: (r1_tarski(A_140, C_141) | ~r1_tarski(A_140, k2_xboole_0(k1_xboole_0, C_141)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_522])).
% 7.83/2.90  tff(c_1889, plain, (![C_142]: (r1_tarski(k2_xboole_0(k1_xboole_0, C_142), C_142))), inference(resolution, [status(thm)], [c_8, c_1734])).
% 7.83/2.90  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.83/2.90  tff(c_1914, plain, (![C_142]: (k2_xboole_0(k1_xboole_0, C_142)=C_142 | ~r1_tarski(C_142, k2_xboole_0(k1_xboole_0, C_142)))), inference(resolution, [status(thm)], [c_1889, c_4])).
% 7.83/2.90  tff(c_1994, plain, (![C_143]: (k2_xboole_0(k1_xboole_0, C_143)=C_143)), inference(demodulation, [status(thm), theory('equality')], [c_1022, c_1914])).
% 7.83/2.90  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.83/2.90  tff(c_2046, plain, (![C_143]: (k2_xboole_0(C_143, k1_xboole_0)=C_143)), inference(superposition, [status(thm), theory('equality')], [c_1994, c_2])).
% 7.83/2.90  tff(c_3696, plain, (![A_212, B_213, C_214]: (k4_xboole_0(A_212, B_213)=C_214 | ~r1_tarski(C_214, k4_xboole_0(A_212, B_213)) | ~r1_tarski(A_212, k2_xboole_0(B_213, C_214)))), inference(resolution, [status(thm)], [c_522, c_4])).
% 7.83/2.90  tff(c_3769, plain, (![A_212, B_213]: (k4_xboole_0(A_212, B_213)=k1_xboole_0 | ~r1_tarski(A_212, k2_xboole_0(B_213, k1_xboole_0)))), inference(resolution, [status(thm)], [c_12, c_3696])).
% 7.83/2.90  tff(c_3802, plain, (![A_215, B_216]: (k4_xboole_0(A_215, B_216)=k1_xboole_0 | ~r1_tarski(A_215, B_216))), inference(demodulation, [status(thm), theory('equality')], [c_2046, c_3769])).
% 7.83/2.90  tff(c_3976, plain, (k4_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_3802])).
% 7.83/2.90  tff(c_4030, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3976, c_22])).
% 7.83/2.90  tff(c_4052, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_4030])).
% 7.83/2.90  tff(c_222, plain, (![A_47, B_48]: (r1_tarski(k3_xboole_0(A_47, B_48), A_47))), inference(superposition, [status(thm), theory('equality')], [c_201, c_14])).
% 7.83/2.90  tff(c_225, plain, (![B_41, A_42]: (r1_tarski(k3_xboole_0(B_41, A_42), A_42))), inference(superposition, [status(thm), theory('equality')], [c_150, c_222])).
% 7.83/2.90  tff(c_4651, plain, (![B_224, A_225]: (k4_xboole_0(k3_xboole_0(B_224, A_225), A_225)=k1_xboole_0)), inference(resolution, [status(thm)], [c_225, c_3802])).
% 7.83/2.90  tff(c_4718, plain, (![B_224, A_225]: (k4_xboole_0(k3_xboole_0(B_224, A_225), k1_xboole_0)=k3_xboole_0(k3_xboole_0(B_224, A_225), A_225))), inference(superposition, [status(thm), theory('equality')], [c_4651, c_22])).
% 7.83/2.90  tff(c_13966, plain, (![B_347, A_348]: (k3_xboole_0(k3_xboole_0(B_347, A_348), A_348)=k3_xboole_0(B_347, A_348))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_4718])).
% 7.83/2.90  tff(c_15811, plain, (![A_362, B_363]: (k3_xboole_0(k3_xboole_0(A_362, B_363), A_362)=k3_xboole_0(B_363, A_362))), inference(superposition, [status(thm), theory('equality')], [c_150, c_13966])).
% 7.83/2.90  tff(c_16072, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4052, c_15811])).
% 7.83/2.90  tff(c_16149, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_452, c_16072])).
% 7.83/2.90  tff(c_30, plain, (![B_27, A_26]: (k3_xboole_0(k1_relat_1(B_27), A_26)=k1_relat_1(k7_relat_1(B_27, A_26)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.83/2.90  tff(c_16530, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16149, c_30])).
% 7.83/2.90  tff(c_16606, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_16530])).
% 7.83/2.90  tff(c_16608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_16606])).
% 7.83/2.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.83/2.90  
% 7.83/2.90  Inference rules
% 7.83/2.90  ----------------------
% 7.83/2.90  #Ref     : 0
% 7.83/2.90  #Sup     : 4099
% 7.83/2.90  #Fact    : 0
% 7.83/2.90  #Define  : 0
% 7.83/2.90  #Split   : 2
% 7.83/2.90  #Chain   : 0
% 7.83/2.90  #Close   : 0
% 7.83/2.90  
% 7.83/2.90  Ordering : KBO
% 7.83/2.90  
% 7.83/2.90  Simplification rules
% 7.83/2.90  ----------------------
% 7.83/2.90  #Subsume      : 497
% 7.83/2.90  #Demod        : 3775
% 7.83/2.90  #Tautology    : 2542
% 7.83/2.90  #SimpNegUnit  : 1
% 7.83/2.90  #BackRed      : 3
% 7.83/2.90  
% 7.83/2.90  #Partial instantiations: 0
% 7.83/2.90  #Strategies tried      : 1
% 7.83/2.90  
% 7.83/2.90  Timing (in seconds)
% 7.83/2.90  ----------------------
% 7.83/2.90  Preprocessing        : 0.30
% 7.83/2.90  Parsing              : 0.16
% 7.83/2.90  CNF conversion       : 0.02
% 7.83/2.90  Main loop            : 1.85
% 7.83/2.90  Inferencing          : 0.41
% 7.83/2.91  Reduction            : 0.95
% 7.83/2.91  Demodulation         : 0.81
% 7.83/2.91  BG Simplification    : 0.05
% 7.83/2.91  Subsumption          : 0.35
% 7.83/2.91  Abstraction          : 0.07
% 7.83/2.91  MUC search           : 0.00
% 7.83/2.91  Cooper               : 0.00
% 7.83/2.91  Total                : 2.18
% 7.83/2.91  Index Insertion      : 0.00
% 7.83/2.91  Index Deletion       : 0.00
% 7.83/2.91  Index Matching       : 0.00
% 7.83/2.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
