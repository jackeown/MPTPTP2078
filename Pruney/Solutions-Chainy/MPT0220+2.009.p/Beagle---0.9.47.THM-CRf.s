%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:05 EST 2020

% Result     : Theorem 5.50s
% Output     : CNFRefutation 5.50s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 170 expanded)
%              Number of leaves         :   29 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :   44 ( 153 expanded)
%              Number of equality atoms :   39 ( 148 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k2_xboole_0(A_59,B_60)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_119,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_112])).

tff(c_235,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k4_xboole_0(B_77,A_76)) = k2_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_247,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k2_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_235])).

tff(c_258,plain,(
    ! [A_78] : k5_xboole_0(A_78,k1_xboole_0) = A_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_247])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_264,plain,(
    ! [A_78] : k5_xboole_0(k1_xboole_0,A_78) = A_78 ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_4])).

tff(c_42,plain,(
    ! [A_49,B_50] : r1_tarski(k1_tarski(A_49),k2_tarski(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_172,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(A_64,B_65) = k1_xboole_0
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_179,plain,(
    ! [A_49,B_50] : k4_xboole_0(k1_tarski(A_49),k2_tarski(A_49,B_50)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_172])).

tff(c_26,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_371,plain,(
    ! [A_84,B_85,C_86] : k5_xboole_0(k5_xboole_0(A_84,B_85),C_86) = k5_xboole_0(A_84,k5_xboole_0(B_85,C_86)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_686,plain,(
    ! [B_110,A_111,B_112] : k5_xboole_0(B_110,k5_xboole_0(A_111,B_112)) = k5_xboole_0(A_111,k5_xboole_0(B_112,B_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_371])).

tff(c_872,plain,(
    ! [A_113,B_114] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_113,B_114)) = k5_xboole_0(B_114,A_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_686])).

tff(c_934,plain,(
    ! [B_20,A_19] : k5_xboole_0(k4_xboole_0(B_20,A_19),A_19) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_19,B_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_872])).

tff(c_1046,plain,(
    ! [B_117,A_118] : k5_xboole_0(k4_xboole_0(B_117,A_118),A_118) = k2_xboole_0(A_118,B_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_934])).

tff(c_1100,plain,(
    ! [A_49,B_50] : k2_xboole_0(k2_tarski(A_49,B_50),k1_tarski(A_49)) = k5_xboole_0(k1_xboole_0,k2_tarski(A_49,B_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_1046])).

tff(c_1128,plain,(
    ! [A_49,B_50] : k2_xboole_0(k2_tarski(A_49,B_50),k1_tarski(A_49)) = k2_tarski(A_49,B_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_1100])).

tff(c_960,plain,(
    ! [B_20,A_19] : k5_xboole_0(k4_xboole_0(B_20,A_19),A_19) = k2_xboole_0(A_19,B_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_934])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_207,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k4_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_219,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_207])).

tff(c_919,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_872])).

tff(c_957,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k4_xboole_0(B_2,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_919])).

tff(c_18,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2781,plain,(
    ! [A_151,B_152,C_153] : k5_xboole_0(A_151,k5_xboole_0(k3_xboole_0(A_151,B_152),C_153)) = k5_xboole_0(k4_xboole_0(A_151,B_152),C_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_371])).

tff(c_2903,plain,(
    ! [A_1,B_2] : k5_xboole_0(k4_xboole_0(A_1,B_2),B_2) = k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_957,c_2781])).

tff(c_2991,plain,(
    ! [B_154,A_155] : k2_xboole_0(B_154,A_155) = k2_xboole_0(A_155,B_154) ),
    inference(demodulation,[status(thm),theory(equality)],[c_960,c_26,c_2903])).

tff(c_3063,plain,(
    ! [A_49,B_50] : k2_xboole_0(k1_tarski(A_49),k2_tarski(A_49,B_50)) = k2_tarski(A_49,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_1128,c_2991])).

tff(c_44,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3063,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.50/2.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.50/2.17  
% 5.50/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.50/2.17  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 5.50/2.17  
% 5.50/2.17  %Foreground sorts:
% 5.50/2.17  
% 5.50/2.17  
% 5.50/2.17  %Background operators:
% 5.50/2.17  
% 5.50/2.17  
% 5.50/2.17  %Foreground operators:
% 5.50/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.50/2.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.50/2.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.50/2.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.50/2.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.50/2.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.50/2.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.50/2.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.50/2.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.50/2.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.50/2.17  tff('#skF_2', type, '#skF_2': $i).
% 5.50/2.17  tff('#skF_1', type, '#skF_1': $i).
% 5.50/2.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.50/2.17  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.50/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.50/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.50/2.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.50/2.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.50/2.17  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.50/2.17  
% 5.50/2.18  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 5.50/2.18  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.50/2.18  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.50/2.18  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.50/2.18  tff(f_67, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 5.50/2.18  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.50/2.18  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.50/2.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.50/2.18  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.50/2.18  tff(f_70, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 5.50/2.18  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.50/2.18  tff(c_112, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k2_xboole_0(A_59, B_60))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.50/2.18  tff(c_119, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_112])).
% 5.50/2.18  tff(c_235, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k4_xboole_0(B_77, A_76))=k2_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.50/2.18  tff(c_247, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k2_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_119, c_235])).
% 5.50/2.18  tff(c_258, plain, (![A_78]: (k5_xboole_0(A_78, k1_xboole_0)=A_78)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_247])).
% 5.50/2.18  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.50/2.18  tff(c_264, plain, (![A_78]: (k5_xboole_0(k1_xboole_0, A_78)=A_78)), inference(superposition, [status(thm), theory('equality')], [c_258, c_4])).
% 5.50/2.18  tff(c_42, plain, (![A_49, B_50]: (r1_tarski(k1_tarski(A_49), k2_tarski(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.50/2.18  tff(c_172, plain, (![A_64, B_65]: (k4_xboole_0(A_64, B_65)=k1_xboole_0 | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.50/2.18  tff(c_179, plain, (![A_49, B_50]: (k4_xboole_0(k1_tarski(A_49), k2_tarski(A_49, B_50))=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_172])).
% 5.50/2.18  tff(c_26, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.50/2.18  tff(c_371, plain, (![A_84, B_85, C_86]: (k5_xboole_0(k5_xboole_0(A_84, B_85), C_86)=k5_xboole_0(A_84, k5_xboole_0(B_85, C_86)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.50/2.18  tff(c_686, plain, (![B_110, A_111, B_112]: (k5_xboole_0(B_110, k5_xboole_0(A_111, B_112))=k5_xboole_0(A_111, k5_xboole_0(B_112, B_110)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_371])).
% 5.50/2.18  tff(c_872, plain, (![A_113, B_114]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_113, B_114))=k5_xboole_0(B_114, A_113))), inference(superposition, [status(thm), theory('equality')], [c_264, c_686])).
% 5.50/2.18  tff(c_934, plain, (![B_20, A_19]: (k5_xboole_0(k4_xboole_0(B_20, A_19), A_19)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_19, B_20)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_872])).
% 5.50/2.18  tff(c_1046, plain, (![B_117, A_118]: (k5_xboole_0(k4_xboole_0(B_117, A_118), A_118)=k2_xboole_0(A_118, B_117))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_934])).
% 5.50/2.18  tff(c_1100, plain, (![A_49, B_50]: (k2_xboole_0(k2_tarski(A_49, B_50), k1_tarski(A_49))=k5_xboole_0(k1_xboole_0, k2_tarski(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_179, c_1046])).
% 5.50/2.18  tff(c_1128, plain, (![A_49, B_50]: (k2_xboole_0(k2_tarski(A_49, B_50), k1_tarski(A_49))=k2_tarski(A_49, B_50))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_1100])).
% 5.50/2.18  tff(c_960, plain, (![B_20, A_19]: (k5_xboole_0(k4_xboole_0(B_20, A_19), A_19)=k2_xboole_0(A_19, B_20))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_934])).
% 5.50/2.18  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.50/2.18  tff(c_207, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k4_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.50/2.18  tff(c_219, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_207])).
% 5.50/2.18  tff(c_919, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k5_xboole_0(k1_xboole_0, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_219, c_872])).
% 5.50/2.18  tff(c_957, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k4_xboole_0(B_2, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_919])).
% 5.50/2.18  tff(c_18, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.50/2.18  tff(c_2781, plain, (![A_151, B_152, C_153]: (k5_xboole_0(A_151, k5_xboole_0(k3_xboole_0(A_151, B_152), C_153))=k5_xboole_0(k4_xboole_0(A_151, B_152), C_153))), inference(superposition, [status(thm), theory('equality')], [c_18, c_371])).
% 5.50/2.18  tff(c_2903, plain, (![A_1, B_2]: (k5_xboole_0(k4_xboole_0(A_1, B_2), B_2)=k5_xboole_0(A_1, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_957, c_2781])).
% 5.50/2.18  tff(c_2991, plain, (![B_154, A_155]: (k2_xboole_0(B_154, A_155)=k2_xboole_0(A_155, B_154))), inference(demodulation, [status(thm), theory('equality')], [c_960, c_26, c_2903])).
% 5.50/2.18  tff(c_3063, plain, (![A_49, B_50]: (k2_xboole_0(k1_tarski(A_49), k2_tarski(A_49, B_50))=k2_tarski(A_49, B_50))), inference(superposition, [status(thm), theory('equality')], [c_1128, c_2991])).
% 5.50/2.18  tff(c_44, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.50/2.18  tff(c_4921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3063, c_44])).
% 5.50/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.50/2.18  
% 5.50/2.18  Inference rules
% 5.50/2.18  ----------------------
% 5.50/2.18  #Ref     : 0
% 5.50/2.18  #Sup     : 1207
% 5.50/2.18  #Fact    : 0
% 5.50/2.18  #Define  : 0
% 5.50/2.18  #Split   : 0
% 5.50/2.18  #Chain   : 0
% 5.50/2.18  #Close   : 0
% 5.50/2.18  
% 5.50/2.18  Ordering : KBO
% 5.50/2.18  
% 5.50/2.18  Simplification rules
% 5.50/2.18  ----------------------
% 5.50/2.18  #Subsume      : 112
% 5.50/2.18  #Demod        : 1070
% 5.50/2.18  #Tautology    : 534
% 5.50/2.18  #SimpNegUnit  : 0
% 5.50/2.18  #BackRed      : 1
% 5.50/2.18  
% 5.50/2.18  #Partial instantiations: 0
% 5.50/2.18  #Strategies tried      : 1
% 5.50/2.18  
% 5.50/2.18  Timing (in seconds)
% 5.50/2.18  ----------------------
% 5.50/2.19  Preprocessing        : 0.32
% 5.50/2.19  Parsing              : 0.17
% 5.50/2.19  CNF conversion       : 0.02
% 5.50/2.19  Main loop            : 1.11
% 5.50/2.19  Inferencing          : 0.29
% 5.50/2.19  Reduction            : 0.63
% 5.50/2.19  Demodulation         : 0.56
% 5.50/2.19  BG Simplification    : 0.04
% 5.50/2.19  Subsumption          : 0.11
% 5.50/2.19  Abstraction          : 0.06
% 5.50/2.19  MUC search           : 0.00
% 5.50/2.19  Cooper               : 0.00
% 5.50/2.19  Total                : 1.45
% 5.50/2.19  Index Insertion      : 0.00
% 5.50/2.19  Index Deletion       : 0.00
% 5.50/2.19  Index Matching       : 0.00
% 5.50/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
