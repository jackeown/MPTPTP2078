%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:59 EST 2020

% Result     : Theorem 8.29s
% Output     : CNFRefutation 8.29s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 141 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :   62 ( 146 expanded)
%              Number of equality atoms :   48 ( 114 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_348,plain,(
    ! [A_51,B_52] : k4_xboole_0(k2_xboole_0(A_51,B_52),B_52) = k4_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_379,plain,(
    ! [A_51] : k4_xboole_0(A_51,k1_xboole_0) = k2_xboole_0(A_51,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_10])).

tff(c_391,plain,(
    ! [A_51] : k2_xboole_0(A_51,k1_xboole_0) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_379])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_57,plain,(
    ! [A_30,B_31] : r1_xboole_0(k4_xboole_0(A_30,B_31),B_31) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_60,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_57])).

tff(c_62,plain,(
    ! [B_33,A_34] :
      ( r1_xboole_0(B_33,A_34)
      | ~ r1_xboole_0(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [A_8] : r1_xboole_0(k1_xboole_0,A_8) ),
    inference(resolution,[status(thm)],[c_60,c_62])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(k2_xboole_0(A_9,B_10),B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(k2_xboole_0(A_23,B_24),B_24) = A_23
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_83,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,B_39) = A_38
      | ~ r1_xboole_0(A_38,B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_26])).

tff(c_97,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_67,c_83])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_200,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_252,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_200])).

tff(c_256,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_252])).

tff(c_22,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1169,plain,(
    ! [A_87,B_88] : k4_xboole_0(k4_xboole_0(A_87,B_88),B_88) = k4_xboole_0(A_87,B_88) ),
    inference(resolution,[status(thm)],[c_22,c_83])).

tff(c_1205,plain,(
    ! [A_87,B_88] : k4_xboole_0(k4_xboole_0(A_87,B_88),k4_xboole_0(A_87,B_88)) = k3_xboole_0(k4_xboole_0(A_87,B_88),B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_1169,c_16])).

tff(c_1288,plain,(
    ! [A_89,B_90] : k3_xboole_0(k4_xboole_0(A_89,B_90),B_90) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_1205])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] : k4_xboole_0(k3_xboole_0(A_15,B_16),C_17) = k3_xboole_0(A_15,k4_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1308,plain,(
    ! [A_89,B_90,C_17] : k3_xboole_0(k4_xboole_0(A_89,B_90),k4_xboole_0(B_90,C_17)) = k4_xboole_0(k1_xboole_0,C_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_1288,c_18])).

tff(c_1353,plain,(
    ! [A_89,B_90,C_17] : k3_xboole_0(k4_xboole_0(A_89,B_90),k4_xboole_0(B_90,C_17)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_1308])).

tff(c_800,plain,(
    ! [A_70,B_71,C_72] : k4_xboole_0(k3_xboole_0(A_70,B_71),C_72) = k3_xboole_0(A_70,k4_xboole_0(B_71,C_72)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1469,plain,(
    ! [A_95,B_96] : k3_xboole_0(A_95,k4_xboole_0(B_96,k3_xboole_0(A_95,B_96))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_800])).

tff(c_1495,plain,(
    ! [A_95,B_96] : k4_xboole_0(A_95,k4_xboole_0(B_96,k3_xboole_0(A_95,B_96))) = k4_xboole_0(A_95,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1469,c_14])).

tff(c_2389,plain,(
    ! [A_112,B_113] : k4_xboole_0(A_112,k4_xboole_0(B_113,k3_xboole_0(A_112,B_113))) = A_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1495])).

tff(c_68,plain,(
    ! [B_20,A_19] : r1_xboole_0(B_20,k4_xboole_0(A_19,B_20)) ),
    inference(resolution,[status(thm)],[c_22,c_62])).

tff(c_96,plain,(
    ! [B_20,A_19] : k4_xboole_0(B_20,k4_xboole_0(A_19,B_20)) = B_20 ),
    inference(resolution,[status(thm)],[c_68,c_83])).

tff(c_1337,plain,(
    ! [B_20,A_19] : k3_xboole_0(B_20,k4_xboole_0(A_19,B_20)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_1288])).

tff(c_5631,plain,(
    ! [B_179,A_180] : k3_xboole_0(k4_xboole_0(B_179,k3_xboole_0(A_180,B_179)),A_180) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2389,c_1337])).

tff(c_5731,plain,(
    ! [B_90,C_17,A_89] : k3_xboole_0(k4_xboole_0(k4_xboole_0(B_90,C_17),k1_xboole_0),k4_xboole_0(A_89,B_90)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1353,c_5631])).

tff(c_6343,plain,(
    ! [B_187,C_188,A_189] : k3_xboole_0(k4_xboole_0(B_187,C_188),k4_xboole_0(A_189,B_187)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_5731])).

tff(c_257,plain,(
    ! [A_47] : k4_xboole_0(A_47,A_47) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_252])).

tff(c_262,plain,(
    ! [A_47] : k4_xboole_0(A_47,k1_xboole_0) = k3_xboole_0(A_47,A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_16])).

tff(c_295,plain,(
    ! [A_47] : k3_xboole_0(A_47,A_47) = A_47 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_262])).

tff(c_878,plain,(
    ! [A_47,C_72] : k3_xboole_0(A_47,k4_xboole_0(A_47,C_72)) = k4_xboole_0(A_47,C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_800])).

tff(c_6614,plain,(
    ! [B_190,C_191] : k4_xboole_0(k4_xboole_0(B_190,C_191),B_190) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6343,c_878])).

tff(c_6896,plain,(
    ! [A_192,B_193] : k4_xboole_0(k3_xboole_0(A_192,B_193),A_192) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_6614])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_7018,plain,(
    ! [A_192,B_193] : k2_xboole_0(k4_xboole_0(A_192,k3_xboole_0(A_192,B_193)),k1_xboole_0) = k5_xboole_0(A_192,k3_xboole_0(A_192,B_193)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6896,c_2])).

tff(c_7153,plain,(
    ! [A_192,B_193] : k5_xboole_0(A_192,k3_xboole_0(A_192,B_193)) = k4_xboole_0(A_192,B_193) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_391,c_7018])).

tff(c_30,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7153,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:40:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.29/3.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.29/3.14  
% 8.29/3.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.29/3.14  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 8.29/3.14  
% 8.29/3.14  %Foreground sorts:
% 8.29/3.14  
% 8.29/3.14  
% 8.29/3.14  %Background operators:
% 8.29/3.14  
% 8.29/3.14  
% 8.29/3.14  %Foreground operators:
% 8.29/3.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.29/3.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.29/3.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.29/3.14  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.29/3.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.29/3.14  tff('#skF_2', type, '#skF_2': $i).
% 8.29/3.14  tff('#skF_1', type, '#skF_1': $i).
% 8.29/3.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.29/3.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.29/3.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.29/3.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.29/3.14  
% 8.29/3.15  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.29/3.15  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.29/3.15  tff(f_41, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 8.29/3.15  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.29/3.15  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 8.29/3.15  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.29/3.15  tff(f_57, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 8.29/3.15  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 8.29/3.15  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 8.29/3.15  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 8.29/3.15  tff(f_62, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.29/3.15  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.29/3.15  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.29/3.15  tff(c_348, plain, (![A_51, B_52]: (k4_xboole_0(k2_xboole_0(A_51, B_52), B_52)=k4_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.29/3.15  tff(c_379, plain, (![A_51]: (k4_xboole_0(A_51, k1_xboole_0)=k2_xboole_0(A_51, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_348, c_10])).
% 8.29/3.15  tff(c_391, plain, (![A_51]: (k2_xboole_0(A_51, k1_xboole_0)=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_379])).
% 8.29/3.15  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.29/3.15  tff(c_57, plain, (![A_30, B_31]: (r1_xboole_0(k4_xboole_0(A_30, B_31), B_31))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.29/3.15  tff(c_60, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_57])).
% 8.29/3.15  tff(c_62, plain, (![B_33, A_34]: (r1_xboole_0(B_33, A_34) | ~r1_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.29/3.15  tff(c_67, plain, (![A_8]: (r1_xboole_0(k1_xboole_0, A_8))), inference(resolution, [status(thm)], [c_60, c_62])).
% 8.29/3.15  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(k2_xboole_0(A_9, B_10), B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.29/3.15  tff(c_26, plain, (![A_23, B_24]: (k4_xboole_0(k2_xboole_0(A_23, B_24), B_24)=A_23 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.29/3.15  tff(c_83, plain, (![A_38, B_39]: (k4_xboole_0(A_38, B_39)=A_38 | ~r1_xboole_0(A_38, B_39))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_26])).
% 8.29/3.15  tff(c_97, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_67, c_83])).
% 8.29/3.15  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.29/3.15  tff(c_200, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.29/3.15  tff(c_252, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_200])).
% 8.29/3.15  tff(c_256, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_252])).
% 8.29/3.15  tff(c_22, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.29/3.15  tff(c_1169, plain, (![A_87, B_88]: (k4_xboole_0(k4_xboole_0(A_87, B_88), B_88)=k4_xboole_0(A_87, B_88))), inference(resolution, [status(thm)], [c_22, c_83])).
% 8.29/3.15  tff(c_1205, plain, (![A_87, B_88]: (k4_xboole_0(k4_xboole_0(A_87, B_88), k4_xboole_0(A_87, B_88))=k3_xboole_0(k4_xboole_0(A_87, B_88), B_88))), inference(superposition, [status(thm), theory('equality')], [c_1169, c_16])).
% 8.29/3.15  tff(c_1288, plain, (![A_89, B_90]: (k3_xboole_0(k4_xboole_0(A_89, B_90), B_90)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_256, c_1205])).
% 8.29/3.15  tff(c_18, plain, (![A_15, B_16, C_17]: (k4_xboole_0(k3_xboole_0(A_15, B_16), C_17)=k3_xboole_0(A_15, k4_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.29/3.15  tff(c_1308, plain, (![A_89, B_90, C_17]: (k3_xboole_0(k4_xboole_0(A_89, B_90), k4_xboole_0(B_90, C_17))=k4_xboole_0(k1_xboole_0, C_17))), inference(superposition, [status(thm), theory('equality')], [c_1288, c_18])).
% 8.29/3.15  tff(c_1353, plain, (![A_89, B_90, C_17]: (k3_xboole_0(k4_xboole_0(A_89, B_90), k4_xboole_0(B_90, C_17))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_97, c_1308])).
% 8.29/3.15  tff(c_800, plain, (![A_70, B_71, C_72]: (k4_xboole_0(k3_xboole_0(A_70, B_71), C_72)=k3_xboole_0(A_70, k4_xboole_0(B_71, C_72)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.29/3.15  tff(c_1469, plain, (![A_95, B_96]: (k3_xboole_0(A_95, k4_xboole_0(B_96, k3_xboole_0(A_95, B_96)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_256, c_800])).
% 8.29/3.15  tff(c_1495, plain, (![A_95, B_96]: (k4_xboole_0(A_95, k4_xboole_0(B_96, k3_xboole_0(A_95, B_96)))=k4_xboole_0(A_95, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1469, c_14])).
% 8.29/3.15  tff(c_2389, plain, (![A_112, B_113]: (k4_xboole_0(A_112, k4_xboole_0(B_113, k3_xboole_0(A_112, B_113)))=A_112)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1495])).
% 8.29/3.15  tff(c_68, plain, (![B_20, A_19]: (r1_xboole_0(B_20, k4_xboole_0(A_19, B_20)))), inference(resolution, [status(thm)], [c_22, c_62])).
% 8.29/3.15  tff(c_96, plain, (![B_20, A_19]: (k4_xboole_0(B_20, k4_xboole_0(A_19, B_20))=B_20)), inference(resolution, [status(thm)], [c_68, c_83])).
% 8.29/3.15  tff(c_1337, plain, (![B_20, A_19]: (k3_xboole_0(B_20, k4_xboole_0(A_19, B_20))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_96, c_1288])).
% 8.29/3.15  tff(c_5631, plain, (![B_179, A_180]: (k3_xboole_0(k4_xboole_0(B_179, k3_xboole_0(A_180, B_179)), A_180)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2389, c_1337])).
% 8.29/3.15  tff(c_5731, plain, (![B_90, C_17, A_89]: (k3_xboole_0(k4_xboole_0(k4_xboole_0(B_90, C_17), k1_xboole_0), k4_xboole_0(A_89, B_90))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1353, c_5631])).
% 8.29/3.15  tff(c_6343, plain, (![B_187, C_188, A_189]: (k3_xboole_0(k4_xboole_0(B_187, C_188), k4_xboole_0(A_189, B_187))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_5731])).
% 8.29/3.15  tff(c_257, plain, (![A_47]: (k4_xboole_0(A_47, A_47)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_252])).
% 8.29/3.15  tff(c_262, plain, (![A_47]: (k4_xboole_0(A_47, k1_xboole_0)=k3_xboole_0(A_47, A_47))), inference(superposition, [status(thm), theory('equality')], [c_257, c_16])).
% 8.29/3.15  tff(c_295, plain, (![A_47]: (k3_xboole_0(A_47, A_47)=A_47)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_262])).
% 8.29/3.15  tff(c_878, plain, (![A_47, C_72]: (k3_xboole_0(A_47, k4_xboole_0(A_47, C_72))=k4_xboole_0(A_47, C_72))), inference(superposition, [status(thm), theory('equality')], [c_295, c_800])).
% 8.29/3.15  tff(c_6614, plain, (![B_190, C_191]: (k4_xboole_0(k4_xboole_0(B_190, C_191), B_190)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6343, c_878])).
% 8.29/3.15  tff(c_6896, plain, (![A_192, B_193]: (k4_xboole_0(k3_xboole_0(A_192, B_193), A_192)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_6614])).
% 8.29/3.15  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k4_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.29/3.15  tff(c_7018, plain, (![A_192, B_193]: (k2_xboole_0(k4_xboole_0(A_192, k3_xboole_0(A_192, B_193)), k1_xboole_0)=k5_xboole_0(A_192, k3_xboole_0(A_192, B_193)))), inference(superposition, [status(thm), theory('equality')], [c_6896, c_2])).
% 8.29/3.15  tff(c_7153, plain, (![A_192, B_193]: (k5_xboole_0(A_192, k3_xboole_0(A_192, B_193))=k4_xboole_0(A_192, B_193))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_391, c_7018])).
% 8.29/3.15  tff(c_30, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.29/3.15  tff(c_22242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7153, c_30])).
% 8.29/3.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.29/3.15  
% 8.29/3.15  Inference rules
% 8.29/3.15  ----------------------
% 8.29/3.15  #Ref     : 1
% 8.29/3.15  #Sup     : 5508
% 8.29/3.15  #Fact    : 0
% 8.29/3.15  #Define  : 0
% 8.29/3.15  #Split   : 0
% 8.29/3.15  #Chain   : 0
% 8.29/3.15  #Close   : 0
% 8.29/3.15  
% 8.29/3.15  Ordering : KBO
% 8.29/3.15  
% 8.29/3.15  Simplification rules
% 8.29/3.15  ----------------------
% 8.29/3.15  #Subsume      : 20
% 8.29/3.15  #Demod        : 6263
% 8.29/3.15  #Tautology    : 4236
% 8.29/3.15  #SimpNegUnit  : 0
% 8.29/3.15  #BackRed      : 1
% 8.29/3.15  
% 8.29/3.15  #Partial instantiations: 0
% 8.29/3.15  #Strategies tried      : 1
% 8.29/3.15  
% 8.29/3.15  Timing (in seconds)
% 8.29/3.15  ----------------------
% 8.29/3.15  Preprocessing        : 0.28
% 8.29/3.15  Parsing              : 0.15
% 8.29/3.16  CNF conversion       : 0.02
% 8.29/3.16  Main loop            : 2.10
% 8.29/3.16  Inferencing          : 0.55
% 8.29/3.16  Reduction            : 1.03
% 8.29/3.16  Demodulation         : 0.88
% 8.29/3.16  BG Simplification    : 0.06
% 8.29/3.16  Subsumption          : 0.34
% 8.29/3.16  Abstraction          : 0.11
% 8.29/3.16  MUC search           : 0.00
% 8.29/3.16  Cooper               : 0.00
% 8.29/3.16  Total                : 2.41
% 8.29/3.16  Index Insertion      : 0.00
% 8.29/3.16  Index Deletion       : 0.00
% 8.29/3.16  Index Matching       : 0.00
% 8.29/3.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
