%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:10 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :   55 (  94 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :   41 (  90 expanded)
%              Number of equality atoms :   33 (  70 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_28,plain,(
    ! [B_14] : r1_tarski(B_14,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_123,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(A_49,B_50) = k1_xboole_0
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_135,plain,(
    ! [B_14] : k4_xboole_0(B_14,B_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_123])).

tff(c_196,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k4_xboole_0(B_63,A_62)) = k2_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_208,plain,(
    ! [B_14] : k5_xboole_0(B_14,k1_xboole_0) = k2_xboole_0(B_14,B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_196])).

tff(c_216,plain,(
    ! [B_64] : k5_xboole_0(B_64,k1_xboole_0) = B_64 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_208])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_222,plain,(
    ! [B_64] : k5_xboole_0(k1_xboole_0,B_64) = B_64 ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_2])).

tff(c_52,plain,(
    ! [A_37,B_38] : r1_tarski(k1_tarski(A_37),k2_tarski(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_134,plain,(
    ! [A_37,B_38] : k4_xboole_0(k1_tarski(A_37),k2_tarski(A_37,B_38)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_123])).

tff(c_42,plain,(
    ! [A_25,B_26] : k5_xboole_0(A_25,k4_xboole_0(B_26,A_25)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_592,plain,(
    ! [A_84,B_85,C_86] : k5_xboole_0(k5_xboole_0(A_84,B_85),C_86) = k5_xboole_0(A_84,k5_xboole_0(B_85,C_86)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1515,plain,(
    ! [A_120,A_118,B_119] : k5_xboole_0(A_120,k5_xboole_0(A_118,B_119)) = k5_xboole_0(A_118,k5_xboole_0(B_119,A_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_592])).

tff(c_1898,plain,(
    ! [B_124,A_125] : k5_xboole_0(k1_xboole_0,k5_xboole_0(B_124,A_125)) = k5_xboole_0(A_125,B_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_1515])).

tff(c_2007,plain,(
    ! [B_26,A_25] : k5_xboole_0(k4_xboole_0(B_26,A_25),A_25) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_25,B_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1898])).

tff(c_2048,plain,(
    ! [B_126,A_127] : k5_xboole_0(k4_xboole_0(B_126,A_127),A_127) = k2_xboole_0(A_127,B_126) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_2007])).

tff(c_2123,plain,(
    ! [A_37,B_38] : k2_xboole_0(k2_tarski(A_37,B_38),k1_tarski(A_37)) = k5_xboole_0(k1_xboole_0,k2_tarski(A_37,B_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_2048])).

tff(c_2339,plain,(
    ! [A_135,B_136] : k2_xboole_0(k2_tarski(A_135,B_136),k1_tarski(A_135)) = k2_tarski(A_135,B_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_2123])).

tff(c_34,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1159,plain,(
    ! [A_107,B_108,C_109] : k5_xboole_0(k5_xboole_0(A_107,B_108),C_109) = k5_xboole_0(B_108,k5_xboole_0(A_107,C_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_592])).

tff(c_40,plain,(
    ! [A_23,B_24] : k5_xboole_0(k5_xboole_0(A_23,B_24),k3_xboole_0(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1199,plain,(
    ! [B_108,A_107] : k5_xboole_0(B_108,k5_xboole_0(A_107,k3_xboole_0(A_107,B_108))) = k2_xboole_0(A_107,B_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_1159,c_40])).

tff(c_1297,plain,(
    ! [B_108,A_107] : k2_xboole_0(B_108,A_107) = k2_xboole_0(A_107,B_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34,c_1199])).

tff(c_2345,plain,(
    ! [A_135,B_136] : k2_xboole_0(k1_tarski(A_135),k2_tarski(A_135,B_136)) = k2_tarski(A_135,B_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_2339,c_1297])).

tff(c_54,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),k2_tarski('#skF_2','#skF_3')) != k2_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2345,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:59:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.76  
% 3.95/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.76  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.95/1.76  
% 3.95/1.76  %Foreground sorts:
% 3.95/1.76  
% 3.95/1.76  
% 3.95/1.76  %Background operators:
% 3.95/1.76  
% 3.95/1.76  
% 3.95/1.76  %Foreground operators:
% 3.95/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.95/1.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.95/1.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.95/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.95/1.76  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.95/1.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.95/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.95/1.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.95/1.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.95/1.76  tff('#skF_2', type, '#skF_2': $i).
% 3.95/1.76  tff('#skF_3', type, '#skF_3': $i).
% 3.95/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.95/1.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.95/1.76  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.95/1.76  
% 3.95/1.77  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.95/1.77  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.95/1.77  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.95/1.77  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.95/1.77  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.95/1.77  tff(f_73, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 3.95/1.77  tff(f_59, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.95/1.77  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.95/1.77  tff(f_61, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.95/1.77  tff(f_76, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 3.95/1.77  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.95/1.77  tff(c_28, plain, (![B_14]: (r1_tarski(B_14, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.95/1.77  tff(c_123, plain, (![A_49, B_50]: (k4_xboole_0(A_49, B_50)=k1_xboole_0 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.95/1.77  tff(c_135, plain, (![B_14]: (k4_xboole_0(B_14, B_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_123])).
% 3.95/1.77  tff(c_196, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k4_xboole_0(B_63, A_62))=k2_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.95/1.77  tff(c_208, plain, (![B_14]: (k5_xboole_0(B_14, k1_xboole_0)=k2_xboole_0(B_14, B_14))), inference(superposition, [status(thm), theory('equality')], [c_135, c_196])).
% 3.95/1.77  tff(c_216, plain, (![B_64]: (k5_xboole_0(B_64, k1_xboole_0)=B_64)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_208])).
% 3.95/1.77  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.95/1.77  tff(c_222, plain, (![B_64]: (k5_xboole_0(k1_xboole_0, B_64)=B_64)), inference(superposition, [status(thm), theory('equality')], [c_216, c_2])).
% 3.95/1.77  tff(c_52, plain, (![A_37, B_38]: (r1_tarski(k1_tarski(A_37), k2_tarski(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.95/1.77  tff(c_134, plain, (![A_37, B_38]: (k4_xboole_0(k1_tarski(A_37), k2_tarski(A_37, B_38))=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_123])).
% 3.95/1.77  tff(c_42, plain, (![A_25, B_26]: (k5_xboole_0(A_25, k4_xboole_0(B_26, A_25))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.95/1.77  tff(c_592, plain, (![A_84, B_85, C_86]: (k5_xboole_0(k5_xboole_0(A_84, B_85), C_86)=k5_xboole_0(A_84, k5_xboole_0(B_85, C_86)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.95/1.77  tff(c_1515, plain, (![A_120, A_118, B_119]: (k5_xboole_0(A_120, k5_xboole_0(A_118, B_119))=k5_xboole_0(A_118, k5_xboole_0(B_119, A_120)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_592])).
% 3.95/1.77  tff(c_1898, plain, (![B_124, A_125]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(B_124, A_125))=k5_xboole_0(A_125, B_124))), inference(superposition, [status(thm), theory('equality')], [c_222, c_1515])).
% 3.95/1.77  tff(c_2007, plain, (![B_26, A_25]: (k5_xboole_0(k4_xboole_0(B_26, A_25), A_25)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_25, B_26)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1898])).
% 3.95/1.77  tff(c_2048, plain, (![B_126, A_127]: (k5_xboole_0(k4_xboole_0(B_126, A_127), A_127)=k2_xboole_0(A_127, B_126))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_2007])).
% 3.95/1.77  tff(c_2123, plain, (![A_37, B_38]: (k2_xboole_0(k2_tarski(A_37, B_38), k1_tarski(A_37))=k5_xboole_0(k1_xboole_0, k2_tarski(A_37, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_134, c_2048])).
% 3.95/1.77  tff(c_2339, plain, (![A_135, B_136]: (k2_xboole_0(k2_tarski(A_135, B_136), k1_tarski(A_135))=k2_tarski(A_135, B_136))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_2123])).
% 3.95/1.77  tff(c_34, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.95/1.77  tff(c_1159, plain, (![A_107, B_108, C_109]: (k5_xboole_0(k5_xboole_0(A_107, B_108), C_109)=k5_xboole_0(B_108, k5_xboole_0(A_107, C_109)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_592])).
% 3.95/1.77  tff(c_40, plain, (![A_23, B_24]: (k5_xboole_0(k5_xboole_0(A_23, B_24), k3_xboole_0(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.95/1.77  tff(c_1199, plain, (![B_108, A_107]: (k5_xboole_0(B_108, k5_xboole_0(A_107, k3_xboole_0(A_107, B_108)))=k2_xboole_0(A_107, B_108))), inference(superposition, [status(thm), theory('equality')], [c_1159, c_40])).
% 3.95/1.77  tff(c_1297, plain, (![B_108, A_107]: (k2_xboole_0(B_108, A_107)=k2_xboole_0(A_107, B_108))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34, c_1199])).
% 3.95/1.77  tff(c_2345, plain, (![A_135, B_136]: (k2_xboole_0(k1_tarski(A_135), k2_tarski(A_135, B_136))=k2_tarski(A_135, B_136))), inference(superposition, [status(thm), theory('equality')], [c_2339, c_1297])).
% 3.95/1.77  tff(c_54, plain, (k2_xboole_0(k1_tarski('#skF_2'), k2_tarski('#skF_2', '#skF_3'))!=k2_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.95/1.77  tff(c_2366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2345, c_54])).
% 3.95/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.77  
% 3.95/1.77  Inference rules
% 3.95/1.77  ----------------------
% 3.95/1.77  #Ref     : 0
% 3.95/1.77  #Sup     : 588
% 3.95/1.77  #Fact    : 0
% 3.95/1.77  #Define  : 0
% 3.95/1.77  #Split   : 0
% 3.95/1.77  #Chain   : 0
% 3.95/1.77  #Close   : 0
% 3.95/1.77  
% 3.95/1.77  Ordering : KBO
% 3.95/1.77  
% 3.95/1.77  Simplification rules
% 3.95/1.77  ----------------------
% 3.95/1.77  #Subsume      : 32
% 3.95/1.77  #Demod        : 322
% 3.95/1.77  #Tautology    : 268
% 3.95/1.77  #SimpNegUnit  : 0
% 3.95/1.77  #BackRed      : 5
% 3.95/1.77  
% 3.95/1.77  #Partial instantiations: 0
% 3.95/1.77  #Strategies tried      : 1
% 3.95/1.77  
% 3.95/1.77  Timing (in seconds)
% 3.95/1.77  ----------------------
% 3.95/1.78  Preprocessing        : 0.39
% 3.95/1.78  Parsing              : 0.22
% 3.95/1.78  CNF conversion       : 0.02
% 3.95/1.78  Main loop            : 0.61
% 3.95/1.78  Inferencing          : 0.20
% 3.95/1.78  Reduction            : 0.27
% 3.95/1.78  Demodulation         : 0.23
% 3.95/1.78  BG Simplification    : 0.03
% 3.95/1.78  Subsumption          : 0.09
% 3.95/1.78  Abstraction          : 0.04
% 3.95/1.78  MUC search           : 0.00
% 3.95/1.78  Cooper               : 0.00
% 3.95/1.78  Total                : 1.04
% 3.95/1.78  Index Insertion      : 0.00
% 3.95/1.78  Index Deletion       : 0.00
% 3.95/1.78  Index Matching       : 0.00
% 3.95/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
