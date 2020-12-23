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
% DateTime   : Thu Dec  3 09:44:58 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :   57 (  92 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  90 expanded)
%              Number of equality atoms :   46 (  77 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_154,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_162,plain,(
    ! [A_7,B_8] : k4_xboole_0(k4_xboole_0(A_7,B_8),A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_154])).

tff(c_256,plain,(
    ! [A_46,B_47] : k5_xboole_0(A_46,k4_xboole_0(B_47,A_46)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_275,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k5_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_256])).

tff(c_283,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_275])).

tff(c_712,plain,(
    ! [A_66,B_67,C_68] : k4_xboole_0(k4_xboole_0(A_66,B_67),C_68) = k4_xboole_0(A_66,k2_xboole_0(B_67,C_68)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_754,plain,(
    ! [C_68,B_67] : k4_xboole_0(C_68,k2_xboole_0(B_67,C_68)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_712,c_162])).

tff(c_26,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_445,plain,(
    ! [A_57,B_58] : k4_xboole_0(k2_xboole_0(A_57,B_58),B_58) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_464,plain,(
    ! [B_58,A_57] : k5_xboole_0(B_58,k4_xboole_0(A_57,B_58)) = k2_xboole_0(B_58,k2_xboole_0(A_57,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_26])).

tff(c_2001,plain,(
    ! [B_101,A_102] : k2_xboole_0(B_101,k2_xboole_0(A_102,B_101)) = k2_xboole_0(B_101,A_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_464])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(k2_xboole_0(A_9,B_10),B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2026,plain,(
    ! [B_101,A_102] : k4_xboole_0(k2_xboole_0(B_101,A_102),k2_xboole_0(A_102,B_101)) = k4_xboole_0(B_101,k2_xboole_0(A_102,B_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2001,c_12])).

tff(c_2057,plain,(
    ! [B_101,A_102] : k4_xboole_0(k2_xboole_0(B_101,A_102),k2_xboole_0(A_102,B_101)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_754,c_2026])).

tff(c_2257,plain,(
    ! [B_107,A_108] : k4_xboole_0(k2_xboole_0(B_107,A_108),k2_xboole_0(A_108,B_107)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_754,c_2026])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | k4_xboole_0(B_6,A_5) != k4_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2274,plain,(
    ! [B_107,A_108] :
      ( k2_xboole_0(B_107,A_108) = k2_xboole_0(A_108,B_107)
      | k4_xboole_0(k2_xboole_0(A_108,B_107),k2_xboole_0(B_107,A_108)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2257,c_8])).

tff(c_2340,plain,(
    ! [B_107,A_108] : k2_xboole_0(B_107,A_108) = k2_xboole_0(A_108,B_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_2274])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_56,plain,(
    ! [B_29,A_30] : k5_xboole_0(B_29,A_30) = k5_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    ! [A_30] : k5_xboole_0(k1_xboole_0,A_30) = A_30 ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_20])).

tff(c_24,plain,(
    ! [A_22] : k5_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_993,plain,(
    ! [A_74,B_75,C_76] : k5_xboole_0(k5_xboole_0(A_74,B_75),C_76) = k5_xboole_0(A_74,k5_xboole_0(B_75,C_76)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1057,plain,(
    ! [A_22,C_76] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_76)) = k5_xboole_0(k1_xboole_0,C_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_993])).

tff(c_1293,plain,(
    ! [A_82,C_83] : k5_xboole_0(A_82,k5_xboole_0(A_82,C_83)) = C_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1057])).

tff(c_1360,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k5_xboole_0(B_85,A_84)) = B_85 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1293])).

tff(c_3369,plain,(
    ! [B_127,A_128] : k5_xboole_0(k4_xboole_0(B_127,A_128),k2_xboole_0(A_128,B_127)) = A_128 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1360])).

tff(c_3465,plain,(
    ! [A_16,B_17] : k5_xboole_0(k3_xboole_0(A_16,B_17),k2_xboole_0(k4_xboole_0(A_16,B_17),A_16)) = k4_xboole_0(A_16,B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3369])).

tff(c_3496,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_283,c_2340,c_3465])).

tff(c_28,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3601,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3496,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.81  
% 3.93/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.81  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.93/1.81  
% 3.93/1.81  %Foreground sorts:
% 3.93/1.81  
% 3.93/1.81  
% 3.93/1.81  %Background operators:
% 3.93/1.81  
% 3.93/1.81  
% 3.93/1.81  %Foreground operators:
% 3.93/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.93/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.93/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.93/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.93/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.93/1.81  tff('#skF_2', type, '#skF_2': $i).
% 3.93/1.81  tff('#skF_1', type, '#skF_1': $i).
% 3.93/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.93/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.93/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.93/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.93/1.81  
% 4.07/1.83  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.07/1.83  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.07/1.83  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.07/1.83  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.07/1.83  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.07/1.83  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.07/1.83  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.07/1.83  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 4.07/1.83  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.07/1.83  tff(f_51, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.07/1.83  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.07/1.83  tff(f_56, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.07/1.83  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.07/1.83  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.07/1.83  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.07/1.83  tff(c_154, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.07/1.83  tff(c_162, plain, (![A_7, B_8]: (k4_xboole_0(k4_xboole_0(A_7, B_8), A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_154])).
% 4.07/1.83  tff(c_256, plain, (![A_46, B_47]: (k5_xboole_0(A_46, k4_xboole_0(B_47, A_46))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.07/1.83  tff(c_275, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k5_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_162, c_256])).
% 4.07/1.83  tff(c_283, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(A_7, B_8))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_275])).
% 4.07/1.83  tff(c_712, plain, (![A_66, B_67, C_68]: (k4_xboole_0(k4_xboole_0(A_66, B_67), C_68)=k4_xboole_0(A_66, k2_xboole_0(B_67, C_68)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.07/1.83  tff(c_754, plain, (![C_68, B_67]: (k4_xboole_0(C_68, k2_xboole_0(B_67, C_68))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_712, c_162])).
% 4.07/1.83  tff(c_26, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.07/1.83  tff(c_445, plain, (![A_57, B_58]: (k4_xboole_0(k2_xboole_0(A_57, B_58), B_58)=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.07/1.83  tff(c_464, plain, (![B_58, A_57]: (k5_xboole_0(B_58, k4_xboole_0(A_57, B_58))=k2_xboole_0(B_58, k2_xboole_0(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_445, c_26])).
% 4.07/1.83  tff(c_2001, plain, (![B_101, A_102]: (k2_xboole_0(B_101, k2_xboole_0(A_102, B_101))=k2_xboole_0(B_101, A_102))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_464])).
% 4.07/1.83  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(k2_xboole_0(A_9, B_10), B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.07/1.83  tff(c_2026, plain, (![B_101, A_102]: (k4_xboole_0(k2_xboole_0(B_101, A_102), k2_xboole_0(A_102, B_101))=k4_xboole_0(B_101, k2_xboole_0(A_102, B_101)))), inference(superposition, [status(thm), theory('equality')], [c_2001, c_12])).
% 4.07/1.83  tff(c_2057, plain, (![B_101, A_102]: (k4_xboole_0(k2_xboole_0(B_101, A_102), k2_xboole_0(A_102, B_101))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_754, c_2026])).
% 4.07/1.83  tff(c_2257, plain, (![B_107, A_108]: (k4_xboole_0(k2_xboole_0(B_107, A_108), k2_xboole_0(A_108, B_107))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_754, c_2026])).
% 4.07/1.83  tff(c_8, plain, (![B_6, A_5]: (B_6=A_5 | k4_xboole_0(B_6, A_5)!=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.07/1.83  tff(c_2274, plain, (![B_107, A_108]: (k2_xboole_0(B_107, A_108)=k2_xboole_0(A_108, B_107) | k4_xboole_0(k2_xboole_0(A_108, B_107), k2_xboole_0(B_107, A_108))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2257, c_8])).
% 4.07/1.83  tff(c_2340, plain, (![B_107, A_108]: (k2_xboole_0(B_107, A_108)=k2_xboole_0(A_108, B_107))), inference(demodulation, [status(thm), theory('equality')], [c_2057, c_2274])).
% 4.07/1.83  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.07/1.83  tff(c_56, plain, (![B_29, A_30]: (k5_xboole_0(B_29, A_30)=k5_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.07/1.83  tff(c_72, plain, (![A_30]: (k5_xboole_0(k1_xboole_0, A_30)=A_30)), inference(superposition, [status(thm), theory('equality')], [c_56, c_20])).
% 4.07/1.83  tff(c_24, plain, (![A_22]: (k5_xboole_0(A_22, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.07/1.83  tff(c_993, plain, (![A_74, B_75, C_76]: (k5_xboole_0(k5_xboole_0(A_74, B_75), C_76)=k5_xboole_0(A_74, k5_xboole_0(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.07/1.83  tff(c_1057, plain, (![A_22, C_76]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_76))=k5_xboole_0(k1_xboole_0, C_76))), inference(superposition, [status(thm), theory('equality')], [c_24, c_993])).
% 4.07/1.83  tff(c_1293, plain, (![A_82, C_83]: (k5_xboole_0(A_82, k5_xboole_0(A_82, C_83))=C_83)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1057])).
% 4.07/1.83  tff(c_1360, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k5_xboole_0(B_85, A_84))=B_85)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1293])).
% 4.07/1.83  tff(c_3369, plain, (![B_127, A_128]: (k5_xboole_0(k4_xboole_0(B_127, A_128), k2_xboole_0(A_128, B_127))=A_128)), inference(superposition, [status(thm), theory('equality')], [c_26, c_1360])).
% 4.07/1.83  tff(c_3465, plain, (![A_16, B_17]: (k5_xboole_0(k3_xboole_0(A_16, B_17), k2_xboole_0(k4_xboole_0(A_16, B_17), A_16))=k4_xboole_0(A_16, B_17))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3369])).
% 4.07/1.83  tff(c_3496, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_283, c_2340, c_3465])).
% 4.07/1.83  tff(c_28, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.07/1.83  tff(c_3601, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3496, c_28])).
% 4.07/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/1.83  
% 4.07/1.83  Inference rules
% 4.07/1.83  ----------------------
% 4.07/1.83  #Ref     : 1
% 4.07/1.83  #Sup     : 885
% 4.07/1.83  #Fact    : 0
% 4.07/1.83  #Define  : 0
% 4.07/1.83  #Split   : 0
% 4.07/1.83  #Chain   : 0
% 4.07/1.83  #Close   : 0
% 4.07/1.83  
% 4.07/1.83  Ordering : KBO
% 4.07/1.83  
% 4.07/1.83  Simplification rules
% 4.07/1.83  ----------------------
% 4.07/1.83  #Subsume      : 13
% 4.07/1.83  #Demod        : 749
% 4.07/1.83  #Tautology    : 639
% 4.07/1.83  #SimpNegUnit  : 0
% 4.07/1.83  #BackRed      : 4
% 4.07/1.83  
% 4.07/1.83  #Partial instantiations: 0
% 4.07/1.83  #Strategies tried      : 1
% 4.07/1.83  
% 4.07/1.83  Timing (in seconds)
% 4.07/1.83  ----------------------
% 4.07/1.83  Preprocessing        : 0.27
% 4.07/1.83  Parsing              : 0.15
% 4.07/1.83  CNF conversion       : 0.02
% 4.07/1.83  Main loop            : 0.70
% 4.07/1.83  Inferencing          : 0.24
% 4.07/1.83  Reduction            : 0.28
% 4.07/1.83  Demodulation         : 0.23
% 4.07/1.83  BG Simplification    : 0.03
% 4.07/1.83  Subsumption          : 0.09
% 4.07/1.83  Abstraction          : 0.04
% 4.07/1.83  MUC search           : 0.00
% 4.07/1.83  Cooper               : 0.00
% 4.07/1.83  Total                : 1.00
% 4.07/1.83  Index Insertion      : 0.00
% 4.07/1.83  Index Deletion       : 0.00
% 4.07/1.83  Index Matching       : 0.00
% 4.07/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
