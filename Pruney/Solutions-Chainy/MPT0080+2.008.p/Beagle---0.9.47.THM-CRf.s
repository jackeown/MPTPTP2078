%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:50 EST 2020

% Result     : Theorem 4.88s
% Output     : CNFRefutation 4.88s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 268 expanded)
%              Number of leaves         :   22 ( 103 expanded)
%              Depth                    :   14
%              Number of atoms          :   65 ( 290 expanded)
%              Number of equality atoms :   50 ( 228 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_122,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | k4_xboole_0(A_28,B_29) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_126,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_122,c_24])).

tff(c_14,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_127,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_142,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_127])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_12,B_13,C_14] : k4_xboole_0(k4_xboole_0(A_12,B_13),C_14) = k4_xboole_0(A_12,k2_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_187,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,B_39) = k1_xboole_0
      | ~ r1_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_195,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_187])).

tff(c_20,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_275,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1557,plain,(
    ! [A_78,B_79] : k4_xboole_0(A_78,k3_xboole_0(A_78,B_79)) = k3_xboole_0(A_78,k4_xboole_0(A_78,B_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_275])).

tff(c_1615,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_3')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_1557])).

tff(c_1635,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1615])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_454,plain,(
    ! [A_51,B_52,C_53] : k4_xboole_0(k4_xboole_0(A_51,B_52),C_53) = k4_xboole_0(A_51,k2_xboole_0(B_52,C_53)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3096,plain,(
    ! [A_105,B_106,C_107] : k4_xboole_0(A_105,k2_xboole_0(k4_xboole_0(A_105,B_106),C_107)) = k4_xboole_0(k3_xboole_0(A_105,B_106),C_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_454])).

tff(c_144,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k2_xboole_0(A_32,B_33)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_127])).

tff(c_151,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_144])).

tff(c_3307,plain,(
    ! [C_108,B_109] : k4_xboole_0(k3_xboole_0(C_108,B_109),C_108) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3096,c_151])).

tff(c_3829,plain,(
    ! [A_117,B_118] : k4_xboole_0(k3_xboole_0(A_117,B_118),B_118) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3307])).

tff(c_299,plain,(
    ! [A_17,B_18] : k3_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_275])).

tff(c_308,plain,(
    ! [A_17,B_18] : k3_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_299])).

tff(c_200,plain,(
    ! [A_40,B_41] : k4_xboole_0(k2_xboole_0(A_40,B_41),B_41) = k4_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_795,plain,(
    ! [A_62,B_63] : k4_xboole_0(k2_xboole_0(A_62,B_63),A_62) = k4_xboole_0(B_63,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_200])).

tff(c_804,plain,(
    ! [A_62,B_63] : k4_xboole_0(k2_xboole_0(A_62,B_63),k4_xboole_0(B_63,A_62)) = k3_xboole_0(k2_xboole_0(A_62,B_63),A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_795,c_20])).

tff(c_849,plain,(
    ! [A_64,B_65] : k4_xboole_0(k2_xboole_0(A_64,B_65),k4_xboole_0(B_65,A_64)) = A_64 ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_4,c_804])).

tff(c_912,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),k4_xboole_0(A_1,B_2)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_849])).

tff(c_3843,plain,(
    ! [A_117,B_118] : k4_xboole_0(k2_xboole_0(k3_xboole_0(A_117,B_118),B_118),k1_xboole_0) = B_118 ),
    inference(superposition,[status(thm),theory(equality)],[c_3829,c_912])).

tff(c_4151,plain,(
    ! [B_122,A_123] : k2_xboole_0(B_122,k3_xboole_0(A_123,B_122)) = B_122 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2,c_3843])).

tff(c_4291,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_1') = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1635,c_4151])).

tff(c_4405,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_1')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4291,c_912])).

tff(c_4463,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_142,c_2,c_18,c_4405])).

tff(c_207,plain,(
    ! [A_40] : k4_xboole_0(A_40,k1_xboole_0) = k2_xboole_0(A_40,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_14])).

tff(c_222,plain,(
    ! [A_40] : k2_xboole_0(A_40,k1_xboole_0) = A_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_207])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_29,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_143,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_29,c_127])).

tff(c_471,plain,(
    ! [A_51,B_52,B_16] : k4_xboole_0(A_51,k2_xboole_0(B_52,k4_xboole_0(k4_xboole_0(A_51,B_52),B_16))) = k3_xboole_0(k4_xboole_0(A_51,B_52),B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_20])).

tff(c_5511,plain,(
    ! [A_138,B_139,B_140] : k4_xboole_0(A_138,k2_xboole_0(B_139,k4_xboole_0(A_138,k2_xboole_0(B_139,B_140)))) = k3_xboole_0(k4_xboole_0(A_138,B_139),B_140) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_471])).

tff(c_5716,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k1_xboole_0)) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_5511])).

tff(c_5780,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4463,c_4,c_4463,c_222,c_4,c_5716])).

tff(c_3381,plain,(
    ! [A_3,B_4] : k4_xboole_0(k3_xboole_0(A_3,B_4),B_4) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3307])).

tff(c_5795,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5780,c_3381])).

tff(c_5815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_5795])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.88/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/1.96  
% 4.88/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/1.96  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.88/1.96  
% 4.88/1.96  %Foreground sorts:
% 4.88/1.96  
% 4.88/1.96  
% 4.88/1.96  %Background operators:
% 4.88/1.96  
% 4.88/1.96  
% 4.88/1.96  %Foreground operators:
% 4.88/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.88/1.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.88/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.88/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.88/1.96  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.88/1.96  tff('#skF_2', type, '#skF_2': $i).
% 4.88/1.96  tff('#skF_3', type, '#skF_3': $i).
% 4.88/1.96  tff('#skF_1', type, '#skF_1': $i).
% 4.88/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.88/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.88/1.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.88/1.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.88/1.96  
% 4.88/1.97  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.88/1.97  tff(f_54, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 4.88/1.97  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.88/1.97  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.88/1.97  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.88/1.97  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.88/1.97  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.88/1.97  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.88/1.97  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.88/1.97  tff(f_41, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.88/1.97  tff(c_122, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | k4_xboole_0(A_28, B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.88/1.97  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.88/1.97  tff(c_126, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_122, c_24])).
% 4.88/1.97  tff(c_14, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.88/1.97  tff(c_22, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.88/1.97  tff(c_127, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.88/1.97  tff(c_142, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k2_xboole_0(A_17, B_18))=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_127])).
% 4.88/1.97  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.88/1.97  tff(c_18, plain, (![A_12, B_13, C_14]: (k4_xboole_0(k4_xboole_0(A_12, B_13), C_14)=k4_xboole_0(A_12, k2_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.88/1.97  tff(c_26, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.88/1.97  tff(c_187, plain, (![A_38, B_39]: (k3_xboole_0(A_38, B_39)=k1_xboole_0 | ~r1_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.88/1.97  tff(c_195, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_187])).
% 4.88/1.97  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.88/1.97  tff(c_275, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.88/1.97  tff(c_1557, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k3_xboole_0(A_78, B_79))=k3_xboole_0(A_78, k4_xboole_0(A_78, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_275])).
% 4.88/1.97  tff(c_1615, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_3'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_195, c_1557])).
% 4.88/1.97  tff(c_1635, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1615])).
% 4.88/1.97  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.88/1.97  tff(c_454, plain, (![A_51, B_52, C_53]: (k4_xboole_0(k4_xboole_0(A_51, B_52), C_53)=k4_xboole_0(A_51, k2_xboole_0(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.88/1.97  tff(c_3096, plain, (![A_105, B_106, C_107]: (k4_xboole_0(A_105, k2_xboole_0(k4_xboole_0(A_105, B_106), C_107))=k4_xboole_0(k3_xboole_0(A_105, B_106), C_107))), inference(superposition, [status(thm), theory('equality')], [c_20, c_454])).
% 4.88/1.97  tff(c_144, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k2_xboole_0(A_32, B_33))=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_127])).
% 4.88/1.97  tff(c_151, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_144])).
% 4.88/1.97  tff(c_3307, plain, (![C_108, B_109]: (k4_xboole_0(k3_xboole_0(C_108, B_109), C_108)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3096, c_151])).
% 4.88/1.97  tff(c_3829, plain, (![A_117, B_118]: (k4_xboole_0(k3_xboole_0(A_117, B_118), B_118)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_3307])).
% 4.88/1.97  tff(c_299, plain, (![A_17, B_18]: (k3_xboole_0(A_17, k2_xboole_0(A_17, B_18))=k4_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_142, c_275])).
% 4.88/1.97  tff(c_308, plain, (![A_17, B_18]: (k3_xboole_0(A_17, k2_xboole_0(A_17, B_18))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_299])).
% 4.88/1.97  tff(c_200, plain, (![A_40, B_41]: (k4_xboole_0(k2_xboole_0(A_40, B_41), B_41)=k4_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.88/1.97  tff(c_795, plain, (![A_62, B_63]: (k4_xboole_0(k2_xboole_0(A_62, B_63), A_62)=k4_xboole_0(B_63, A_62))), inference(superposition, [status(thm), theory('equality')], [c_2, c_200])).
% 4.88/1.97  tff(c_804, plain, (![A_62, B_63]: (k4_xboole_0(k2_xboole_0(A_62, B_63), k4_xboole_0(B_63, A_62))=k3_xboole_0(k2_xboole_0(A_62, B_63), A_62))), inference(superposition, [status(thm), theory('equality')], [c_795, c_20])).
% 4.88/1.97  tff(c_849, plain, (![A_64, B_65]: (k4_xboole_0(k2_xboole_0(A_64, B_65), k4_xboole_0(B_65, A_64))=A_64)), inference(demodulation, [status(thm), theory('equality')], [c_308, c_4, c_804])).
% 4.88/1.97  tff(c_912, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), k4_xboole_0(A_1, B_2))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_849])).
% 4.88/1.97  tff(c_3843, plain, (![A_117, B_118]: (k4_xboole_0(k2_xboole_0(k3_xboole_0(A_117, B_118), B_118), k1_xboole_0)=B_118)), inference(superposition, [status(thm), theory('equality')], [c_3829, c_912])).
% 4.88/1.97  tff(c_4151, plain, (![B_122, A_123]: (k2_xboole_0(B_122, k3_xboole_0(A_123, B_122))=B_122)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2, c_3843])).
% 4.88/1.97  tff(c_4291, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_1')=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1635, c_4151])).
% 4.88/1.97  tff(c_4405, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_1'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_4291, c_912])).
% 4.88/1.97  tff(c_4463, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_142, c_2, c_18, c_4405])).
% 4.88/1.97  tff(c_207, plain, (![A_40]: (k4_xboole_0(A_40, k1_xboole_0)=k2_xboole_0(A_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_200, c_14])).
% 4.88/1.97  tff(c_222, plain, (![A_40]: (k2_xboole_0(A_40, k1_xboole_0)=A_40)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_207])).
% 4.88/1.97  tff(c_28, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.88/1.97  tff(c_29, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 4.88/1.97  tff(c_143, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_29, c_127])).
% 4.88/1.97  tff(c_471, plain, (![A_51, B_52, B_16]: (k4_xboole_0(A_51, k2_xboole_0(B_52, k4_xboole_0(k4_xboole_0(A_51, B_52), B_16)))=k3_xboole_0(k4_xboole_0(A_51, B_52), B_16))), inference(superposition, [status(thm), theory('equality')], [c_454, c_20])).
% 4.88/1.97  tff(c_5511, plain, (![A_138, B_139, B_140]: (k4_xboole_0(A_138, k2_xboole_0(B_139, k4_xboole_0(A_138, k2_xboole_0(B_139, B_140))))=k3_xboole_0(k4_xboole_0(A_138, B_139), B_140))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_471])).
% 4.88/1.97  tff(c_5716, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k1_xboole_0))=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_143, c_5511])).
% 4.88/1.97  tff(c_5780, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4463, c_4, c_4463, c_222, c_4, c_5716])).
% 4.88/1.97  tff(c_3381, plain, (![A_3, B_4]: (k4_xboole_0(k3_xboole_0(A_3, B_4), B_4)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_3307])).
% 4.88/1.97  tff(c_5795, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5780, c_3381])).
% 4.88/1.97  tff(c_5815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_5795])).
% 4.88/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/1.97  
% 4.88/1.97  Inference rules
% 4.88/1.97  ----------------------
% 4.88/1.97  #Ref     : 0
% 4.88/1.97  #Sup     : 1430
% 4.88/1.97  #Fact    : 0
% 4.88/1.97  #Define  : 0
% 4.88/1.97  #Split   : 0
% 4.88/1.97  #Chain   : 0
% 4.88/1.97  #Close   : 0
% 4.88/1.97  
% 4.88/1.97  Ordering : KBO
% 4.88/1.97  
% 4.88/1.97  Simplification rules
% 4.88/1.97  ----------------------
% 4.88/1.97  #Subsume      : 8
% 4.88/1.97  #Demod        : 1329
% 4.88/1.97  #Tautology    : 976
% 4.88/1.97  #SimpNegUnit  : 1
% 4.88/1.97  #BackRed      : 5
% 4.88/1.97  
% 4.88/1.97  #Partial instantiations: 0
% 4.88/1.97  #Strategies tried      : 1
% 4.88/1.97  
% 4.88/1.97  Timing (in seconds)
% 4.88/1.97  ----------------------
% 4.88/1.98  Preprocessing        : 0.26
% 4.88/1.98  Parsing              : 0.14
% 4.88/1.98  CNF conversion       : 0.02
% 4.88/1.98  Main loop            : 0.91
% 4.88/1.98  Inferencing          : 0.26
% 4.88/1.98  Reduction            : 0.43
% 4.88/1.98  Demodulation         : 0.37
% 4.88/1.98  BG Simplification    : 0.03
% 5.08/1.98  Subsumption          : 0.13
% 5.08/1.98  Abstraction          : 0.04
% 5.08/1.98  MUC search           : 0.00
% 5.08/1.98  Cooper               : 0.00
% 5.08/1.98  Total                : 1.20
% 5.08/1.98  Index Insertion      : 0.00
% 5.08/1.98  Index Deletion       : 0.00
% 5.08/1.98  Index Matching       : 0.00
% 5.08/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
