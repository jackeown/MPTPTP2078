%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:54 EST 2020

% Result     : Theorem 9.22s
% Output     : CNFRefutation 9.22s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 105 expanded)
%              Number of leaves         :   22 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :   52 (  95 expanded)
%              Number of equality atoms :   51 (  94 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_212,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_221,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,k4_xboole_0(A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_212])).

tff(c_233,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_221])).

tff(c_18,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_230,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_212])).

tff(c_236,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_230])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_69,plain,(
    ! [B_28,A_29] : k5_xboole_0(B_28,A_29) = k5_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_85,plain,(
    ! [A_29] : k5_xboole_0(k1_xboole_0,A_29) = A_29 ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_18])).

tff(c_281,plain,(
    ! [A_39,B_40] : k5_xboole_0(A_39,k4_xboole_0(B_40,A_39)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_307,plain,(
    ! [A_6] : k5_xboole_0(k1_xboole_0,A_6) = k2_xboole_0(k1_xboole_0,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_281])).

tff(c_316,plain,(
    ! [A_41] : k2_xboole_0(k1_xboole_0,A_41) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_307])).

tff(c_336,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_316])).

tff(c_708,plain,(
    ! [A_54,B_55,C_56] : k3_xboole_0(k4_xboole_0(A_54,B_55),k4_xboole_0(A_54,C_56)) = k4_xboole_0(A_54,k2_xboole_0(B_55,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_755,plain,(
    ! [A_6,B_55] : k4_xboole_0(A_6,k2_xboole_0(B_55,k1_xboole_0)) = k3_xboole_0(k4_xboole_0(A_6,B_55),A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_708])).

tff(c_1914,plain,(
    ! [A_82,B_83] : k3_xboole_0(k4_xboole_0(A_82,B_83),A_82) = k4_xboole_0(A_82,B_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_755])).

tff(c_1951,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(k3_xboole_0(A_12,B_13),A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1914])).

tff(c_2220,plain,(
    ! [A_88,B_89] : k3_xboole_0(k3_xboole_0(A_88,B_89),A_88) = k3_xboole_0(A_88,B_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1951])).

tff(c_2232,plain,(
    ! [A_88,B_89] : k4_xboole_0(k3_xboole_0(A_88,B_89),k3_xboole_0(A_88,B_89)) = k4_xboole_0(k3_xboole_0(A_88,B_89),A_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_2220,c_12])).

tff(c_2291,plain,(
    ! [A_90,B_91] : k4_xboole_0(k3_xboole_0(A_90,B_91),A_90) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_2232])).

tff(c_24,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2317,plain,(
    ! [A_90,B_91] : k2_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k5_xboole_0(A_90,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2291,c_24])).

tff(c_2381,plain,(
    ! [A_92,B_93] : k2_xboole_0(A_92,k3_xboole_0(A_92,B_93)) = A_92 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2317])).

tff(c_2418,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = A_12 ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_2381])).

tff(c_22,plain,(
    ! [A_21] : k5_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_485,plain,(
    ! [A_47,B_48,C_49] : k5_xboole_0(k5_xboole_0(A_47,B_48),C_49) = k5_xboole_0(A_47,k5_xboole_0(B_48,C_49)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_549,plain,(
    ! [A_21,C_49] : k5_xboole_0(A_21,k5_xboole_0(A_21,C_49)) = k5_xboole_0(k1_xboole_0,C_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_485])).

tff(c_563,plain,(
    ! [A_50,C_51] : k5_xboole_0(A_50,k5_xboole_0(A_50,C_51)) = C_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_549])).

tff(c_1520,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k2_xboole_0(A_77,B_78)) = k4_xboole_0(B_78,A_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_563])).

tff(c_606,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_563])).

tff(c_3820,plain,(
    ! [A_116,B_117] : k5_xboole_0(k2_xboole_0(A_116,B_117),k4_xboole_0(B_117,A_116)) = A_116 ),
    inference(superposition,[status(thm),theory(equality)],[c_1520,c_606])).

tff(c_3907,plain,(
    ! [A_12,B_13] : k5_xboole_0(k2_xboole_0(k4_xboole_0(A_12,B_13),A_12),k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3820])).

tff(c_3943,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2418,c_4,c_2,c_3907])).

tff(c_26,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22695,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3943,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:57:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.22/3.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.22/3.69  
% 9.22/3.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.22/3.69  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 9.22/3.69  
% 9.22/3.69  %Foreground sorts:
% 9.22/3.69  
% 9.22/3.69  
% 9.22/3.69  %Background operators:
% 9.22/3.69  
% 9.22/3.69  
% 9.22/3.69  %Foreground operators:
% 9.22/3.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.22/3.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.22/3.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.22/3.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.22/3.69  tff('#skF_2', type, '#skF_2': $i).
% 9.22/3.69  tff('#skF_1', type, '#skF_1': $i).
% 9.22/3.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.22/3.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.22/3.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.22/3.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.22/3.69  
% 9.22/3.70  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 9.22/3.70  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 9.22/3.70  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.22/3.70  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 9.22/3.70  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 9.22/3.70  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.22/3.70  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.22/3.70  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.22/3.70  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 9.22/3.70  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 9.22/3.70  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.22/3.70  tff(f_52, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.22/3.70  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.22/3.70  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.22/3.70  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.22/3.70  tff(c_212, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.22/3.70  tff(c_221, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k3_xboole_0(A_12, k4_xboole_0(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_212])).
% 9.22/3.70  tff(c_233, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_221])).
% 9.22/3.70  tff(c_18, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.22/3.70  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.22/3.70  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.22/3.70  tff(c_230, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_212])).
% 9.22/3.70  tff(c_236, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_230])).
% 9.22/3.70  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.22/3.70  tff(c_69, plain, (![B_28, A_29]: (k5_xboole_0(B_28, A_29)=k5_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.22/3.70  tff(c_85, plain, (![A_29]: (k5_xboole_0(k1_xboole_0, A_29)=A_29)), inference(superposition, [status(thm), theory('equality')], [c_69, c_18])).
% 9.22/3.70  tff(c_281, plain, (![A_39, B_40]: (k5_xboole_0(A_39, k4_xboole_0(B_40, A_39))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.22/3.70  tff(c_307, plain, (![A_6]: (k5_xboole_0(k1_xboole_0, A_6)=k2_xboole_0(k1_xboole_0, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_281])).
% 9.22/3.70  tff(c_316, plain, (![A_41]: (k2_xboole_0(k1_xboole_0, A_41)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_85, c_307])).
% 9.22/3.70  tff(c_336, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_316])).
% 9.22/3.70  tff(c_708, plain, (![A_54, B_55, C_56]: (k3_xboole_0(k4_xboole_0(A_54, B_55), k4_xboole_0(A_54, C_56))=k4_xboole_0(A_54, k2_xboole_0(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.22/3.70  tff(c_755, plain, (![A_6, B_55]: (k4_xboole_0(A_6, k2_xboole_0(B_55, k1_xboole_0))=k3_xboole_0(k4_xboole_0(A_6, B_55), A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_708])).
% 9.22/3.70  tff(c_1914, plain, (![A_82, B_83]: (k3_xboole_0(k4_xboole_0(A_82, B_83), A_82)=k4_xboole_0(A_82, B_83))), inference(demodulation, [status(thm), theory('equality')], [c_336, c_755])).
% 9.22/3.70  tff(c_1951, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(k3_xboole_0(A_12, B_13), A_12))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1914])).
% 9.22/3.70  tff(c_2220, plain, (![A_88, B_89]: (k3_xboole_0(k3_xboole_0(A_88, B_89), A_88)=k3_xboole_0(A_88, B_89))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1951])).
% 9.22/3.70  tff(c_2232, plain, (![A_88, B_89]: (k4_xboole_0(k3_xboole_0(A_88, B_89), k3_xboole_0(A_88, B_89))=k4_xboole_0(k3_xboole_0(A_88, B_89), A_88))), inference(superposition, [status(thm), theory('equality')], [c_2220, c_12])).
% 9.22/3.70  tff(c_2291, plain, (![A_90, B_91]: (k4_xboole_0(k3_xboole_0(A_90, B_91), A_90)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_2232])).
% 9.22/3.70  tff(c_24, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.22/3.70  tff(c_2317, plain, (![A_90, B_91]: (k2_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k5_xboole_0(A_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2291, c_24])).
% 9.22/3.70  tff(c_2381, plain, (![A_92, B_93]: (k2_xboole_0(A_92, k3_xboole_0(A_92, B_93))=A_92)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2317])).
% 9.22/3.70  tff(c_2418, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(A_12, B_13))=A_12)), inference(superposition, [status(thm), theory('equality')], [c_233, c_2381])).
% 9.22/3.70  tff(c_22, plain, (![A_21]: (k5_xboole_0(A_21, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.22/3.70  tff(c_485, plain, (![A_47, B_48, C_49]: (k5_xboole_0(k5_xboole_0(A_47, B_48), C_49)=k5_xboole_0(A_47, k5_xboole_0(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.22/3.70  tff(c_549, plain, (![A_21, C_49]: (k5_xboole_0(A_21, k5_xboole_0(A_21, C_49))=k5_xboole_0(k1_xboole_0, C_49))), inference(superposition, [status(thm), theory('equality')], [c_22, c_485])).
% 9.22/3.70  tff(c_563, plain, (![A_50, C_51]: (k5_xboole_0(A_50, k5_xboole_0(A_50, C_51))=C_51)), inference(demodulation, [status(thm), theory('equality')], [c_85, c_549])).
% 9.22/3.70  tff(c_1520, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k2_xboole_0(A_77, B_78))=k4_xboole_0(B_78, A_77))), inference(superposition, [status(thm), theory('equality')], [c_24, c_563])).
% 9.22/3.70  tff(c_606, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_563])).
% 9.22/3.70  tff(c_3820, plain, (![A_116, B_117]: (k5_xboole_0(k2_xboole_0(A_116, B_117), k4_xboole_0(B_117, A_116))=A_116)), inference(superposition, [status(thm), theory('equality')], [c_1520, c_606])).
% 9.22/3.70  tff(c_3907, plain, (![A_12, B_13]: (k5_xboole_0(k2_xboole_0(k4_xboole_0(A_12, B_13), A_12), k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3820])).
% 9.22/3.70  tff(c_3943, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2418, c_4, c_2, c_3907])).
% 9.22/3.70  tff(c_26, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.22/3.70  tff(c_22695, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3943, c_26])).
% 9.22/3.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.22/3.70  
% 9.22/3.70  Inference rules
% 9.22/3.70  ----------------------
% 9.22/3.70  #Ref     : 0
% 9.22/3.70  #Sup     : 5644
% 9.22/3.70  #Fact    : 0
% 9.22/3.70  #Define  : 0
% 9.22/3.70  #Split   : 0
% 9.22/3.70  #Chain   : 0
% 9.22/3.70  #Close   : 0
% 9.22/3.70  
% 9.22/3.70  Ordering : KBO
% 9.22/3.70  
% 9.22/3.70  Simplification rules
% 9.22/3.70  ----------------------
% 9.22/3.70  #Subsume      : 90
% 9.22/3.70  #Demod        : 6610
% 9.22/3.70  #Tautology    : 3686
% 9.22/3.70  #SimpNegUnit  : 0
% 9.22/3.70  #BackRed      : 4
% 9.22/3.70  
% 9.22/3.70  #Partial instantiations: 0
% 9.22/3.70  #Strategies tried      : 1
% 9.22/3.70  
% 9.22/3.70  Timing (in seconds)
% 9.22/3.70  ----------------------
% 9.22/3.70  Preprocessing        : 0.28
% 9.22/3.70  Parsing              : 0.16
% 9.22/3.70  CNF conversion       : 0.01
% 9.22/3.70  Main loop            : 2.63
% 9.22/3.70  Inferencing          : 0.58
% 9.22/3.70  Reduction            : 1.52
% 9.22/3.70  Demodulation         : 1.37
% 9.22/3.70  BG Simplification    : 0.07
% 9.22/3.70  Subsumption          : 0.34
% 9.22/3.70  Abstraction          : 0.13
% 9.22/3.70  MUC search           : 0.00
% 9.22/3.70  Cooper               : 0.00
% 9.22/3.70  Total                : 2.94
% 9.22/3.70  Index Insertion      : 0.00
% 9.22/3.70  Index Deletion       : 0.00
% 9.22/3.71  Index Matching       : 0.00
% 9.22/3.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
