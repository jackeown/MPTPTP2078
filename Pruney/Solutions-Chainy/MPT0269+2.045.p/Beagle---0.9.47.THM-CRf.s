%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:49 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   62 (  91 expanded)
%              Number of leaves         :   32 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :   49 (  82 expanded)
%              Number of equality atoms :   43 (  76 expanded)
%              Maximal formula depth    :   10 (   3 average)
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

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_63,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_12,B_13] : k5_xboole_0(k5_xboole_0(A_12,B_13),k2_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_299,plain,(
    ! [A_75,B_76,C_77] : k5_xboole_0(k5_xboole_0(A_75,B_76),C_77) = k5_xboole_0(A_75,k5_xboole_0(B_76,C_77)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1649,plain,(
    ! [A_127,B_128] : k5_xboole_0(A_127,k5_xboole_0(B_128,k2_xboole_0(A_127,B_128))) = k3_xboole_0(A_127,B_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_299])).

tff(c_38,plain,(
    ! [A_46] : k3_tarski(k1_tarski(A_46)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_105,plain,(
    ! [A_56,B_57] : k3_tarski(k2_tarski(A_56,B_57)) = k2_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_114,plain,(
    ! [A_14] : k3_tarski(k1_tarski(A_14)) = k2_xboole_0(A_14,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_105])).

tff(c_117,plain,(
    ! [A_14] : k2_xboole_0(A_14,A_14) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_114])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_182,plain,(
    ! [A_70,B_71] : k5_xboole_0(k5_xboole_0(A_70,B_71),k2_xboole_0(A_70,B_71)) = k3_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_206,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_11,A_11)) = k3_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_182])).

tff(c_210,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_2,c_206])).

tff(c_367,plain,(
    ! [A_11,C_77] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_77)) = k5_xboole_0(k1_xboole_0,C_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_299])).

tff(c_380,plain,(
    ! [A_11,C_77] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_77)) = C_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_367])).

tff(c_1664,plain,(
    ! [B_128,A_127] : k5_xboole_0(B_128,k2_xboole_0(A_127,B_128)) = k5_xboole_0(A_127,k3_xboole_0(A_127,B_128)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1649,c_380])).

tff(c_1730,plain,(
    ! [B_129,A_130] : k5_xboole_0(B_129,k2_xboole_0(A_130,B_129)) = k4_xboole_0(A_130,B_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1664])).

tff(c_1845,plain,(
    ! [B_133,A_134] : k5_xboole_0(B_133,k4_xboole_0(A_134,B_133)) = k2_xboole_0(A_134,B_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_1730,c_380])).

tff(c_1905,plain,(
    k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) = k2_xboole_0('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1845])).

tff(c_1917,plain,(
    k2_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1905])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1975,plain,(
    r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1917,c_8])).

tff(c_30,plain,(
    ! [B_43,A_42] :
      ( k1_tarski(B_43) = A_42
      | k1_xboole_0 = A_42
      | ~ r1_tarski(A_42,k1_tarski(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1984,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1975,c_30])).

tff(c_1988,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_1984])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.53  
% 3.55/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.54  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.55/1.54  
% 3.55/1.54  %Foreground sorts:
% 3.55/1.54  
% 3.55/1.54  
% 3.55/1.54  %Background operators:
% 3.55/1.54  
% 3.55/1.54  
% 3.55/1.54  %Foreground operators:
% 3.55/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.55/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.55/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.55/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.55/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.55/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.55/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.55/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.55/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.55/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.55/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.55/1.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.55/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.55/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.55/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.55/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.55/1.54  
% 3.55/1.55  tff(f_73, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 3.55/1.55  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.55/1.55  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.55/1.55  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.55/1.55  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.55/1.55  tff(f_63, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 3.55/1.55  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.55/1.55  tff(f_61, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.55/1.55  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.55/1.55  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.55/1.55  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.55/1.55  tff(f_59, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.55/1.55  tff(c_42, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.55/1.55  tff(c_40, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.55/1.55  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.55/1.55  tff(c_44, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.55/1.55  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.55/1.55  tff(c_14, plain, (![A_12, B_13]: (k5_xboole_0(k5_xboole_0(A_12, B_13), k2_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.55/1.55  tff(c_299, plain, (![A_75, B_76, C_77]: (k5_xboole_0(k5_xboole_0(A_75, B_76), C_77)=k5_xboole_0(A_75, k5_xboole_0(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.55/1.55  tff(c_1649, plain, (![A_127, B_128]: (k5_xboole_0(A_127, k5_xboole_0(B_128, k2_xboole_0(A_127, B_128)))=k3_xboole_0(A_127, B_128))), inference(superposition, [status(thm), theory('equality')], [c_14, c_299])).
% 3.55/1.55  tff(c_38, plain, (![A_46]: (k3_tarski(k1_tarski(A_46))=A_46)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.55/1.55  tff(c_16, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.55/1.55  tff(c_105, plain, (![A_56, B_57]: (k3_tarski(k2_tarski(A_56, B_57))=k2_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.55/1.55  tff(c_114, plain, (![A_14]: (k3_tarski(k1_tarski(A_14))=k2_xboole_0(A_14, A_14))), inference(superposition, [status(thm), theory('equality')], [c_16, c_105])).
% 3.55/1.55  tff(c_117, plain, (![A_14]: (k2_xboole_0(A_14, A_14)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_114])).
% 3.55/1.55  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.55/1.55  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.55/1.55  tff(c_182, plain, (![A_70, B_71]: (k5_xboole_0(k5_xboole_0(A_70, B_71), k2_xboole_0(A_70, B_71))=k3_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.55/1.55  tff(c_206, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_11, A_11))=k3_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_12, c_182])).
% 3.55/1.55  tff(c_210, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_117, c_2, c_206])).
% 3.55/1.55  tff(c_367, plain, (![A_11, C_77]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_77))=k5_xboole_0(k1_xboole_0, C_77))), inference(superposition, [status(thm), theory('equality')], [c_12, c_299])).
% 3.55/1.55  tff(c_380, plain, (![A_11, C_77]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_77))=C_77)), inference(demodulation, [status(thm), theory('equality')], [c_210, c_367])).
% 3.55/1.55  tff(c_1664, plain, (![B_128, A_127]: (k5_xboole_0(B_128, k2_xboole_0(A_127, B_128))=k5_xboole_0(A_127, k3_xboole_0(A_127, B_128)))), inference(superposition, [status(thm), theory('equality')], [c_1649, c_380])).
% 3.55/1.55  tff(c_1730, plain, (![B_129, A_130]: (k5_xboole_0(B_129, k2_xboole_0(A_130, B_129))=k4_xboole_0(A_130, B_129))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1664])).
% 3.55/1.55  tff(c_1845, plain, (![B_133, A_134]: (k5_xboole_0(B_133, k4_xboole_0(A_134, B_133))=k2_xboole_0(A_134, B_133))), inference(superposition, [status(thm), theory('equality')], [c_1730, c_380])).
% 3.55/1.55  tff(c_1905, plain, (k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)=k2_xboole_0('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1845])).
% 3.55/1.55  tff(c_1917, plain, (k2_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1905])).
% 3.55/1.55  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.55/1.55  tff(c_1975, plain, (r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1917, c_8])).
% 3.55/1.55  tff(c_30, plain, (![B_43, A_42]: (k1_tarski(B_43)=A_42 | k1_xboole_0=A_42 | ~r1_tarski(A_42, k1_tarski(B_43)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.55/1.55  tff(c_1984, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1975, c_30])).
% 3.55/1.55  tff(c_1988, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_1984])).
% 3.55/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.55  
% 3.55/1.55  Inference rules
% 3.55/1.55  ----------------------
% 3.55/1.55  #Ref     : 0
% 3.55/1.55  #Sup     : 485
% 3.55/1.55  #Fact    : 0
% 3.55/1.55  #Define  : 0
% 3.55/1.55  #Split   : 0
% 3.55/1.55  #Chain   : 0
% 3.55/1.55  #Close   : 0
% 3.55/1.55  
% 3.55/1.55  Ordering : KBO
% 3.55/1.55  
% 3.55/1.55  Simplification rules
% 3.55/1.55  ----------------------
% 3.55/1.55  #Subsume      : 3
% 3.55/1.55  #Demod        : 297
% 3.55/1.55  #Tautology    : 312
% 3.55/1.55  #SimpNegUnit  : 1
% 3.55/1.55  #BackRed      : 3
% 3.55/1.55  
% 3.55/1.55  #Partial instantiations: 0
% 3.55/1.55  #Strategies tried      : 1
% 3.55/1.55  
% 3.55/1.55  Timing (in seconds)
% 3.55/1.55  ----------------------
% 3.55/1.55  Preprocessing        : 0.32
% 3.55/1.55  Parsing              : 0.17
% 3.55/1.55  CNF conversion       : 0.02
% 3.55/1.55  Main loop            : 0.47
% 3.55/1.55  Inferencing          : 0.17
% 3.55/1.55  Reduction            : 0.19
% 3.55/1.55  Demodulation         : 0.15
% 3.55/1.55  BG Simplification    : 0.03
% 3.55/1.55  Subsumption          : 0.06
% 3.55/1.55  Abstraction          : 0.03
% 3.55/1.55  MUC search           : 0.00
% 3.55/1.55  Cooper               : 0.00
% 3.55/1.55  Total                : 0.82
% 3.55/1.55  Index Insertion      : 0.00
% 3.55/1.55  Index Deletion       : 0.00
% 3.55/1.55  Index Matching       : 0.00
% 3.55/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
