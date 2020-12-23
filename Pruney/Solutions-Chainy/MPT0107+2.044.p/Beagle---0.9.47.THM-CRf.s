%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:58 EST 2020

% Result     : Theorem 7.15s
% Output     : CNFRefutation 7.15s
% Verified   : 
% Statistics : Number of formulae       :   63 (  94 expanded)
%              Number of leaves         :   25 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   58 (  89 expanded)
%              Number of equality atoms :   52 (  83 expanded)
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

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_459,plain,(
    ! [A_55,B_56,C_57] : k4_xboole_0(k4_xboole_0(A_55,B_56),C_57) = k4_xboole_0(A_55,k2_xboole_0(B_56,C_57)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8641,plain,(
    ! [A_175,B_176,C_177] : k4_xboole_0(A_175,k2_xboole_0(k4_xboole_0(A_175,B_176),C_177)) = k4_xboole_0(k3_xboole_0(A_175,B_176),C_177) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_459])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_214,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_235,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_214])).

tff(c_245,plain,(
    ! [A_46,B_47] : k3_xboole_0(A_46,k2_xboole_0(A_46,B_47)) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_235])).

tff(c_251,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k2_xboole_0(A_46,B_47)) = k4_xboole_0(A_46,A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_18])).

tff(c_259,plain,(
    ! [A_46] : k4_xboole_0(A_46,A_46) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_251])).

tff(c_472,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k2_xboole_0(B_56,k4_xboole_0(A_55,B_56))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_259])).

tff(c_541,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k2_xboole_0(B_56,A_55)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_472])).

tff(c_8854,plain,(
    ! [C_178,B_179] : k4_xboole_0(k3_xboole_0(C_178,B_179),C_178) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8641,c_541])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_177,plain,(
    ! [A_38,B_39] :
      ( k2_xboole_0(A_38,B_39) = B_39
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_181,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_177])).

tff(c_9177,plain,(
    ! [C_182,B_183] : k2_xboole_0(k3_xboole_0(C_182,B_183),C_182) = C_182 ),
    inference(superposition,[status(thm),theory(equality)],[c_8854,c_181])).

tff(c_28,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_74,plain,(
    ! [B_31,A_32] : k5_xboole_0(B_31,A_32) = k5_xboole_0(A_32,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_90,plain,(
    ! [A_32] : k5_xboole_0(k1_xboole_0,A_32) = A_32 ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_22])).

tff(c_26,plain,(
    ! [A_23] : k5_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_619,plain,(
    ! [A_60,B_61,C_62] : k5_xboole_0(k5_xboole_0(A_60,B_61),C_62) = k5_xboole_0(A_60,k5_xboole_0(B_61,C_62)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_683,plain,(
    ! [A_23,C_62] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_62)) = k5_xboole_0(k1_xboole_0,C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_619])).

tff(c_727,plain,(
    ! [A_64,C_65] : k5_xboole_0(A_64,k5_xboole_0(A_64,C_65)) = C_65 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_683])).

tff(c_1404,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k2_xboole_0(A_84,B_85)) = k4_xboole_0(B_85,A_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_727])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_770,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_727])).

tff(c_1953,plain,(
    ! [A_99,B_100] : k5_xboole_0(k2_xboole_0(A_99,B_100),k4_xboole_0(B_100,A_99)) = A_99 ),
    inference(superposition,[status(thm),theory(equality)],[c_1404,c_770])).

tff(c_696,plain,(
    ! [A_23,C_62] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_62)) = C_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_683])).

tff(c_1968,plain,(
    ! [A_99,B_100] : k5_xboole_0(k2_xboole_0(A_99,B_100),A_99) = k4_xboole_0(B_100,A_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_1953,c_696])).

tff(c_9217,plain,(
    ! [C_182,B_183] : k5_xboole_0(C_182,k3_xboole_0(C_182,B_183)) = k4_xboole_0(C_182,k3_xboole_0(C_182,B_183)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9177,c_1968])).

tff(c_9322,plain,(
    ! [C_182,B_183] : k5_xboole_0(C_182,k3_xboole_0(C_182,B_183)) = k4_xboole_0(C_182,B_183) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_9217])).

tff(c_30,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9322,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n022.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 12:30:11 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.15/2.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.15/2.84  
% 7.15/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.15/2.85  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 7.15/2.85  
% 7.15/2.85  %Foreground sorts:
% 7.15/2.85  
% 7.15/2.85  
% 7.15/2.85  %Background operators:
% 7.15/2.85  
% 7.15/2.85  
% 7.15/2.85  %Foreground operators:
% 7.15/2.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.15/2.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.15/2.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.15/2.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.15/2.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.15/2.85  tff('#skF_2', type, '#skF_2': $i).
% 7.15/2.85  tff('#skF_1', type, '#skF_1': $i).
% 7.15/2.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.15/2.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.15/2.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.15/2.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.15/2.85  
% 7.15/2.86  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 7.15/2.86  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.15/2.86  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 7.15/2.86  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.15/2.86  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 7.15/2.86  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.15/2.86  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.15/2.86  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 7.15/2.86  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.15/2.86  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.15/2.86  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 7.15/2.86  tff(f_53, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 7.15/2.86  tff(f_51, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.15/2.86  tff(f_58, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.15/2.86  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.15/2.86  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.15/2.86  tff(c_459, plain, (![A_55, B_56, C_57]: (k4_xboole_0(k4_xboole_0(A_55, B_56), C_57)=k4_xboole_0(A_55, k2_xboole_0(B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.15/2.86  tff(c_8641, plain, (![A_175, B_176, C_177]: (k4_xboole_0(A_175, k2_xboole_0(k4_xboole_0(A_175, B_176), C_177))=k4_xboole_0(k3_xboole_0(A_175, B_176), C_177))), inference(superposition, [status(thm), theory('equality')], [c_20, c_459])).
% 7.15/2.86  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.15/2.86  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.15/2.86  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.15/2.86  tff(c_214, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.15/2.86  tff(c_235, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k4_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_214])).
% 7.15/2.86  tff(c_245, plain, (![A_46, B_47]: (k3_xboole_0(A_46, k2_xboole_0(A_46, B_47))=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_235])).
% 7.15/2.86  tff(c_251, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k2_xboole_0(A_46, B_47))=k4_xboole_0(A_46, A_46))), inference(superposition, [status(thm), theory('equality')], [c_245, c_18])).
% 7.15/2.86  tff(c_259, plain, (![A_46]: (k4_xboole_0(A_46, A_46)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_251])).
% 7.15/2.86  tff(c_472, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k2_xboole_0(B_56, k4_xboole_0(A_55, B_56)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_459, c_259])).
% 7.15/2.86  tff(c_541, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k2_xboole_0(B_56, A_55))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_472])).
% 7.15/2.86  tff(c_8854, plain, (![C_178, B_179]: (k4_xboole_0(k3_xboole_0(C_178, B_179), C_178)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8641, c_541])).
% 7.15/2.86  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.15/2.86  tff(c_14, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.15/2.86  tff(c_177, plain, (![A_38, B_39]: (k2_xboole_0(A_38, B_39)=B_39 | ~r1_tarski(A_38, B_39))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 7.15/2.86  tff(c_181, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_177])).
% 7.15/2.86  tff(c_9177, plain, (![C_182, B_183]: (k2_xboole_0(k3_xboole_0(C_182, B_183), C_182)=C_182)), inference(superposition, [status(thm), theory('equality')], [c_8854, c_181])).
% 7.15/2.86  tff(c_28, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.15/2.86  tff(c_74, plain, (![B_31, A_32]: (k5_xboole_0(B_31, A_32)=k5_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.15/2.86  tff(c_22, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.15/2.86  tff(c_90, plain, (![A_32]: (k5_xboole_0(k1_xboole_0, A_32)=A_32)), inference(superposition, [status(thm), theory('equality')], [c_74, c_22])).
% 7.15/2.86  tff(c_26, plain, (![A_23]: (k5_xboole_0(A_23, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.15/2.86  tff(c_619, plain, (![A_60, B_61, C_62]: (k5_xboole_0(k5_xboole_0(A_60, B_61), C_62)=k5_xboole_0(A_60, k5_xboole_0(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.15/2.86  tff(c_683, plain, (![A_23, C_62]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_62))=k5_xboole_0(k1_xboole_0, C_62))), inference(superposition, [status(thm), theory('equality')], [c_26, c_619])).
% 7.15/2.86  tff(c_727, plain, (![A_64, C_65]: (k5_xboole_0(A_64, k5_xboole_0(A_64, C_65))=C_65)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_683])).
% 7.15/2.86  tff(c_1404, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k2_xboole_0(A_84, B_85))=k4_xboole_0(B_85, A_84))), inference(superposition, [status(thm), theory('equality')], [c_28, c_727])).
% 7.15/2.86  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.15/2.86  tff(c_770, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_727])).
% 7.15/2.86  tff(c_1953, plain, (![A_99, B_100]: (k5_xboole_0(k2_xboole_0(A_99, B_100), k4_xboole_0(B_100, A_99))=A_99)), inference(superposition, [status(thm), theory('equality')], [c_1404, c_770])).
% 7.15/2.86  tff(c_696, plain, (![A_23, C_62]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_62))=C_62)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_683])).
% 7.15/2.86  tff(c_1968, plain, (![A_99, B_100]: (k5_xboole_0(k2_xboole_0(A_99, B_100), A_99)=k4_xboole_0(B_100, A_99))), inference(superposition, [status(thm), theory('equality')], [c_1953, c_696])).
% 7.15/2.86  tff(c_9217, plain, (![C_182, B_183]: (k5_xboole_0(C_182, k3_xboole_0(C_182, B_183))=k4_xboole_0(C_182, k3_xboole_0(C_182, B_183)))), inference(superposition, [status(thm), theory('equality')], [c_9177, c_1968])).
% 7.15/2.86  tff(c_9322, plain, (![C_182, B_183]: (k5_xboole_0(C_182, k3_xboole_0(C_182, B_183))=k4_xboole_0(C_182, B_183))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_9217])).
% 7.15/2.86  tff(c_30, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.15/2.86  tff(c_14193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9322, c_30])).
% 7.15/2.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.15/2.86  
% 7.15/2.86  Inference rules
% 7.15/2.86  ----------------------
% 7.15/2.86  #Ref     : 0
% 7.15/2.86  #Sup     : 3583
% 7.15/2.86  #Fact    : 0
% 7.15/2.86  #Define  : 0
% 7.15/2.86  #Split   : 0
% 7.15/2.86  #Chain   : 0
% 7.15/2.86  #Close   : 0
% 7.15/2.86  
% 7.15/2.86  Ordering : KBO
% 7.15/2.86  
% 7.15/2.86  Simplification rules
% 7.15/2.86  ----------------------
% 7.15/2.86  #Subsume      : 140
% 7.15/2.86  #Demod        : 3773
% 7.15/2.86  #Tautology    : 2072
% 7.15/2.86  #SimpNegUnit  : 0
% 7.15/2.86  #BackRed      : 3
% 7.15/2.86  
% 7.15/2.86  #Partial instantiations: 0
% 7.15/2.86  #Strategies tried      : 1
% 7.15/2.86  
% 7.15/2.86  Timing (in seconds)
% 7.15/2.86  ----------------------
% 7.15/2.86  Preprocessing        : 0.27
% 7.15/2.86  Parsing              : 0.15
% 7.15/2.86  CNF conversion       : 0.02
% 7.15/2.86  Main loop            : 1.82
% 7.15/2.86  Inferencing          : 0.46
% 7.15/2.86  Reduction            : 1.00
% 7.15/2.86  Demodulation         : 0.89
% 7.15/2.86  BG Simplification    : 0.06
% 7.15/2.86  Subsumption          : 0.22
% 7.15/2.86  Abstraction          : 0.09
% 7.15/2.86  MUC search           : 0.00
% 7.15/2.87  Cooper               : 0.00
% 7.15/2.87  Total                : 2.12
% 7.15/2.87  Index Insertion      : 0.00
% 7.15/2.87  Index Deletion       : 0.00
% 7.15/2.87  Index Matching       : 0.00
% 7.15/2.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
