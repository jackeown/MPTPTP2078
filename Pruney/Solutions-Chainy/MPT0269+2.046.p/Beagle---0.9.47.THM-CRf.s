%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:50 EST 2020

% Result     : Theorem 5.18s
% Output     : CNFRefutation 5.18s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 104 expanded)
%              Number of leaves         :   32 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :   64 ( 111 expanded)
%              Number of equality atoms :   55 ( 102 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_72,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_70,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_44,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_48,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] : k5_xboole_0(k5_xboole_0(A_9,B_10),C_11) = k5_xboole_0(A_9,k5_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_260,plain,(
    ! [A_86,B_87] : k5_xboole_0(k5_xboole_0(A_86,B_87),k2_xboole_0(A_86,B_87)) = k3_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1824,plain,(
    ! [A_144,B_145] : k5_xboole_0(A_144,k5_xboole_0(B_145,k2_xboole_0(A_144,B_145))) = k3_xboole_0(A_144,B_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_260])).

tff(c_42,plain,(
    ! [A_48] : k3_tarski(k1_tarski(A_48)) = A_48 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_138,plain,(
    ! [A_66,B_67] : k3_tarski(k2_tarski(A_66,B_67)) = k2_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_147,plain,(
    ! [A_15] : k3_tarski(k1_tarski(A_15)) = k2_xboole_0(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_138])).

tff(c_150,plain,(
    ! [A_15] : k2_xboole_0(A_15,A_15) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_147])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_297,plain,(
    ! [A_12] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_12,A_12)) = k3_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_260])).

tff(c_301,plain,(
    ! [A_12] : k5_xboole_0(k1_xboole_0,A_12) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_2,c_297])).

tff(c_208,plain,(
    ! [A_83,B_84,C_85] : k5_xboole_0(k5_xboole_0(A_83,B_84),C_85) = k5_xboole_0(A_83,k5_xboole_0(B_84,C_85)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_249,plain,(
    ! [A_12,C_85] : k5_xboole_0(A_12,k5_xboole_0(A_12,C_85)) = k5_xboole_0(k1_xboole_0,C_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_208])).

tff(c_450,plain,(
    ! [A_12,C_85] : k5_xboole_0(A_12,k5_xboole_0(A_12,C_85)) = C_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_249])).

tff(c_1839,plain,(
    ! [B_145,A_144] : k5_xboole_0(B_145,k2_xboole_0(A_144,B_145)) = k5_xboole_0(A_144,k3_xboole_0(A_144,B_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1824,c_450])).

tff(c_1905,plain,(
    ! [B_146,A_147] : k5_xboole_0(B_146,k2_xboole_0(A_147,B_146)) = k4_xboole_0(A_147,B_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1839])).

tff(c_2020,plain,(
    ! [B_150,A_151] : k5_xboole_0(B_150,k4_xboole_0(A_151,B_150)) = k2_xboole_0(A_151,B_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_1905,c_450])).

tff(c_2080,plain,(
    k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) = k2_xboole_0('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_2020])).

tff(c_2092,plain,(
    k2_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2080])).

tff(c_160,plain,(
    ! [A_69,B_70,C_71] : r1_tarski(k3_xboole_0(A_69,B_70),k2_xboole_0(A_69,C_71)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_166,plain,(
    ! [A_1,C_71] : r1_tarski(A_1,k2_xboole_0(A_1,C_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_160])).

tff(c_2150,plain,(
    r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2092,c_166])).

tff(c_985,plain,(
    ! [B_117,C_118,A_119] :
      ( k2_tarski(B_117,C_118) = A_119
      | k1_tarski(C_118) = A_119
      | k1_tarski(B_117) = A_119
      | k1_xboole_0 = A_119
      | ~ r1_tarski(A_119,k2_tarski(B_117,C_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1002,plain,(
    ! [A_15,A_119] :
      ( k2_tarski(A_15,A_15) = A_119
      | k1_tarski(A_15) = A_119
      | k1_tarski(A_15) = A_119
      | k1_xboole_0 = A_119
      | ~ r1_tarski(A_119,k1_tarski(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_985])).

tff(c_4489,plain,(
    ! [A_184,A_185] :
      ( k1_tarski(A_184) = A_185
      | k1_tarski(A_184) = A_185
      | k1_tarski(A_184) = A_185
      | k1_xboole_0 = A_185
      | ~ r1_tarski(A_185,k1_tarski(A_184)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1002])).

tff(c_4495,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2150,c_4489])).

tff(c_4511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_44,c_44,c_4495])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:42:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.18/2.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.18/2.02  
% 5.18/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.18/2.02  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 5.18/2.02  
% 5.18/2.02  %Foreground sorts:
% 5.18/2.02  
% 5.18/2.02  
% 5.18/2.02  %Background operators:
% 5.18/2.02  
% 5.18/2.02  
% 5.18/2.02  %Foreground operators:
% 5.18/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.18/2.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.18/2.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.18/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.18/2.02  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.18/2.02  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.18/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.18/2.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.18/2.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.18/2.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.18/2.02  tff('#skF_2', type, '#skF_2': $i).
% 5.18/2.02  tff('#skF_1', type, '#skF_1': $i).
% 5.18/2.02  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.18/2.02  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.18/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.18/2.02  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.18/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.18/2.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.18/2.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.18/2.02  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.18/2.02  
% 5.18/2.03  tff(f_82, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 5.18/2.03  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.18/2.03  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.18/2.03  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.18/2.03  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 5.18/2.03  tff(f_72, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 5.18/2.03  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.18/2.04  tff(f_70, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.18/2.04  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.18/2.04  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.18/2.04  tff(f_31, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_xboole_1)).
% 5.18/2.04  tff(f_68, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 5.18/2.04  tff(c_46, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.18/2.04  tff(c_44, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.18/2.04  tff(c_8, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.18/2.04  tff(c_48, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.18/2.04  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.18/2.04  tff(c_10, plain, (![A_9, B_10, C_11]: (k5_xboole_0(k5_xboole_0(A_9, B_10), C_11)=k5_xboole_0(A_9, k5_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.18/2.04  tff(c_260, plain, (![A_86, B_87]: (k5_xboole_0(k5_xboole_0(A_86, B_87), k2_xboole_0(A_86, B_87))=k3_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.18/2.04  tff(c_1824, plain, (![A_144, B_145]: (k5_xboole_0(A_144, k5_xboole_0(B_145, k2_xboole_0(A_144, B_145)))=k3_xboole_0(A_144, B_145))), inference(superposition, [status(thm), theory('equality')], [c_10, c_260])).
% 5.18/2.04  tff(c_42, plain, (![A_48]: (k3_tarski(k1_tarski(A_48))=A_48)), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.18/2.04  tff(c_16, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.18/2.04  tff(c_138, plain, (![A_66, B_67]: (k3_tarski(k2_tarski(A_66, B_67))=k2_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.18/2.04  tff(c_147, plain, (![A_15]: (k3_tarski(k1_tarski(A_15))=k2_xboole_0(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_16, c_138])).
% 5.18/2.04  tff(c_150, plain, (![A_15]: (k2_xboole_0(A_15, A_15)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_147])).
% 5.18/2.04  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.18/2.04  tff(c_12, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.18/2.04  tff(c_297, plain, (![A_12]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_12, A_12))=k3_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_12, c_260])).
% 5.18/2.04  tff(c_301, plain, (![A_12]: (k5_xboole_0(k1_xboole_0, A_12)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_150, c_2, c_297])).
% 5.18/2.04  tff(c_208, plain, (![A_83, B_84, C_85]: (k5_xboole_0(k5_xboole_0(A_83, B_84), C_85)=k5_xboole_0(A_83, k5_xboole_0(B_84, C_85)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.18/2.04  tff(c_249, plain, (![A_12, C_85]: (k5_xboole_0(A_12, k5_xboole_0(A_12, C_85))=k5_xboole_0(k1_xboole_0, C_85))), inference(superposition, [status(thm), theory('equality')], [c_12, c_208])).
% 5.18/2.04  tff(c_450, plain, (![A_12, C_85]: (k5_xboole_0(A_12, k5_xboole_0(A_12, C_85))=C_85)), inference(demodulation, [status(thm), theory('equality')], [c_301, c_249])).
% 5.18/2.04  tff(c_1839, plain, (![B_145, A_144]: (k5_xboole_0(B_145, k2_xboole_0(A_144, B_145))=k5_xboole_0(A_144, k3_xboole_0(A_144, B_145)))), inference(superposition, [status(thm), theory('equality')], [c_1824, c_450])).
% 5.18/2.04  tff(c_1905, plain, (![B_146, A_147]: (k5_xboole_0(B_146, k2_xboole_0(A_147, B_146))=k4_xboole_0(A_147, B_146))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1839])).
% 5.18/2.04  tff(c_2020, plain, (![B_150, A_151]: (k5_xboole_0(B_150, k4_xboole_0(A_151, B_150))=k2_xboole_0(A_151, B_150))), inference(superposition, [status(thm), theory('equality')], [c_1905, c_450])).
% 5.18/2.04  tff(c_2080, plain, (k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)=k2_xboole_0('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_2020])).
% 5.18/2.04  tff(c_2092, plain, (k2_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2080])).
% 5.18/2.04  tff(c_160, plain, (![A_69, B_70, C_71]: (r1_tarski(k3_xboole_0(A_69, B_70), k2_xboole_0(A_69, C_71)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.18/2.04  tff(c_166, plain, (![A_1, C_71]: (r1_tarski(A_1, k2_xboole_0(A_1, C_71)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_160])).
% 5.18/2.04  tff(c_2150, plain, (r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2092, c_166])).
% 5.18/2.04  tff(c_985, plain, (![B_117, C_118, A_119]: (k2_tarski(B_117, C_118)=A_119 | k1_tarski(C_118)=A_119 | k1_tarski(B_117)=A_119 | k1_xboole_0=A_119 | ~r1_tarski(A_119, k2_tarski(B_117, C_118)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.18/2.04  tff(c_1002, plain, (![A_15, A_119]: (k2_tarski(A_15, A_15)=A_119 | k1_tarski(A_15)=A_119 | k1_tarski(A_15)=A_119 | k1_xboole_0=A_119 | ~r1_tarski(A_119, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_985])).
% 5.18/2.04  tff(c_4489, plain, (![A_184, A_185]: (k1_tarski(A_184)=A_185 | k1_tarski(A_184)=A_185 | k1_tarski(A_184)=A_185 | k1_xboole_0=A_185 | ~r1_tarski(A_185, k1_tarski(A_184)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1002])).
% 5.18/2.04  tff(c_4495, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_2150, c_4489])).
% 5.18/2.04  tff(c_4511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_44, c_44, c_4495])).
% 5.18/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.18/2.04  
% 5.18/2.04  Inference rules
% 5.18/2.04  ----------------------
% 5.18/2.04  #Ref     : 0
% 5.18/2.04  #Sup     : 1132
% 5.18/2.04  #Fact    : 0
% 5.18/2.04  #Define  : 0
% 5.18/2.04  #Split   : 0
% 5.18/2.04  #Chain   : 0
% 5.18/2.04  #Close   : 0
% 5.18/2.04  
% 5.18/2.04  Ordering : KBO
% 5.18/2.04  
% 5.18/2.04  Simplification rules
% 5.18/2.04  ----------------------
% 5.18/2.04  #Subsume      : 3
% 5.18/2.04  #Demod        : 952
% 5.18/2.04  #Tautology    : 629
% 5.18/2.04  #SimpNegUnit  : 1
% 5.18/2.04  #BackRed      : 3
% 5.18/2.04  
% 5.18/2.04  #Partial instantiations: 0
% 5.18/2.04  #Strategies tried      : 1
% 5.18/2.04  
% 5.18/2.04  Timing (in seconds)
% 5.18/2.04  ----------------------
% 5.18/2.04  Preprocessing        : 0.33
% 5.18/2.04  Parsing              : 0.18
% 5.18/2.04  CNF conversion       : 0.02
% 5.18/2.04  Main loop            : 0.92
% 5.18/2.04  Inferencing          : 0.27
% 5.18/2.04  Reduction            : 0.43
% 5.18/2.04  Demodulation         : 0.37
% 5.18/2.04  BG Simplification    : 0.04
% 5.18/2.04  Subsumption          : 0.13
% 5.18/2.04  Abstraction          : 0.05
% 5.18/2.04  MUC search           : 0.00
% 5.18/2.04  Cooper               : 0.00
% 5.18/2.04  Total                : 1.28
% 5.18/2.04  Index Insertion      : 0.00
% 5.18/2.04  Index Deletion       : 0.00
% 5.18/2.04  Index Matching       : 0.00
% 5.18/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
