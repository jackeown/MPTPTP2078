%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:24 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :   44 (  54 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   42 (  52 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

tff(c_208,plain,(
    ! [A_41,B_42] : k2_xboole_0(k3_xboole_0(A_41,B_42),k4_xboole_0(A_41,B_42)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_25,plain,(
    ! [B_23,A_24] : k2_xboole_0(B_23,A_24) = k2_xboole_0(A_24,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_40,plain,(
    ! [A_24,B_23] : r1_tarski(A_24,k2_xboole_0(B_23,A_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_20])).

tff(c_223,plain,(
    ! [A_41,B_42] : r1_tarski(k4_xboole_0(A_41,B_42),A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_40])).

tff(c_16,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_75,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [A_24,B_23] : k4_xboole_0(A_24,k2_xboole_0(B_23,A_24)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_75])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_266,plain,(
    ! [A_48,B_49,C_50] : k4_xboole_0(k4_xboole_0(A_48,B_49),C_50) = k4_xboole_0(A_48,k2_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_284,plain,(
    ! [C_50,A_48,B_49] : k2_xboole_0(C_50,k4_xboole_0(A_48,k2_xboole_0(B_49,C_50))) = k2_xboole_0(C_50,k4_xboole_0(A_48,B_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_8])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k4_xboole_0(A_7,B_8),C_9) = k4_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_295,plain,(
    ! [A_48,B_49,B_11] : k4_xboole_0(A_48,k2_xboole_0(B_49,k4_xboole_0(k4_xboole_0(A_48,B_49),B_11))) = k3_xboole_0(k4_xboole_0(A_48,B_49),B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_12])).

tff(c_2718,plain,(
    ! [A_113,B_114,B_115] : k4_xboole_0(A_113,k2_xboole_0(B_114,k4_xboole_0(A_113,k2_xboole_0(B_114,B_115)))) = k3_xboole_0(k4_xboole_0(A_113,B_114),B_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_295])).

tff(c_2803,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k2_xboole_0(B_49,k4_xboole_0(A_48,B_49))) = k3_xboole_0(k4_xboole_0(A_48,B_49),B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_2718])).

tff(c_2937,plain,(
    ! [A_116,B_117] : k3_xboole_0(k4_xboole_0(A_116,B_117),B_117) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_8,c_2803])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] :
      ( ~ r1_xboole_0(A_15,k3_xboole_0(B_16,C_17))
      | ~ r1_tarski(A_15,C_17)
      | r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2972,plain,(
    ! [A_15,B_117,A_116] :
      ( ~ r1_xboole_0(A_15,k1_xboole_0)
      | ~ r1_tarski(A_15,B_117)
      | r1_xboole_0(A_15,k4_xboole_0(A_116,B_117)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2937,c_18])).

tff(c_3419,plain,(
    ! [A_126,B_127,A_128] :
      ( ~ r1_tarski(A_126,B_127)
      | r1_xboole_0(A_126,k4_xboole_0(A_128,B_127)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2972])).

tff(c_22,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3422,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3419,c_22])).

tff(c_3465,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_3422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:50:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.84/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.69  
% 3.84/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.69  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.84/1.69  
% 3.84/1.69  %Foreground sorts:
% 3.84/1.69  
% 3.84/1.69  
% 3.84/1.69  %Background operators:
% 3.84/1.69  
% 3.84/1.69  
% 3.84/1.69  %Foreground operators:
% 3.84/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.84/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.84/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.84/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.84/1.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.84/1.69  tff('#skF_2', type, '#skF_2': $i).
% 3.84/1.69  tff('#skF_1', type, '#skF_1': $i).
% 3.84/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.84/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.84/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.84/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.84/1.69  
% 3.84/1.70  tff(f_39, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.84/1.70  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.84/1.70  tff(f_51, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.84/1.70  tff(f_41, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.84/1.70  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.84/1.70  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.84/1.70  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.84/1.70  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.84/1.70  tff(f_49, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 3.84/1.70  tff(f_54, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_xboole_1)).
% 3.84/1.70  tff(c_208, plain, (![A_41, B_42]: (k2_xboole_0(k3_xboole_0(A_41, B_42), k4_xboole_0(A_41, B_42))=A_41)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.84/1.70  tff(c_25, plain, (![B_23, A_24]: (k2_xboole_0(B_23, A_24)=k2_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.84/1.70  tff(c_20, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.84/1.70  tff(c_40, plain, (![A_24, B_23]: (r1_tarski(A_24, k2_xboole_0(B_23, A_24)))), inference(superposition, [status(thm), theory('equality')], [c_25, c_20])).
% 3.84/1.70  tff(c_223, plain, (![A_41, B_42]: (r1_tarski(k4_xboole_0(A_41, B_42), A_41))), inference(superposition, [status(thm), theory('equality')], [c_208, c_40])).
% 3.84/1.70  tff(c_16, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.84/1.70  tff(c_75, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.84/1.70  tff(c_86, plain, (![A_24, B_23]: (k4_xboole_0(A_24, k2_xboole_0(B_23, A_24))=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_75])).
% 3.84/1.70  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.84/1.70  tff(c_266, plain, (![A_48, B_49, C_50]: (k4_xboole_0(k4_xboole_0(A_48, B_49), C_50)=k4_xboole_0(A_48, k2_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.84/1.70  tff(c_284, plain, (![C_50, A_48, B_49]: (k2_xboole_0(C_50, k4_xboole_0(A_48, k2_xboole_0(B_49, C_50)))=k2_xboole_0(C_50, k4_xboole_0(A_48, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_266, c_8])).
% 3.84/1.70  tff(c_10, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k4_xboole_0(A_7, B_8), C_9)=k4_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.84/1.70  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.84/1.70  tff(c_295, plain, (![A_48, B_49, B_11]: (k4_xboole_0(A_48, k2_xboole_0(B_49, k4_xboole_0(k4_xboole_0(A_48, B_49), B_11)))=k3_xboole_0(k4_xboole_0(A_48, B_49), B_11))), inference(superposition, [status(thm), theory('equality')], [c_266, c_12])).
% 3.84/1.70  tff(c_2718, plain, (![A_113, B_114, B_115]: (k4_xboole_0(A_113, k2_xboole_0(B_114, k4_xboole_0(A_113, k2_xboole_0(B_114, B_115))))=k3_xboole_0(k4_xboole_0(A_113, B_114), B_115))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_295])).
% 3.84/1.70  tff(c_2803, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k2_xboole_0(B_49, k4_xboole_0(A_48, B_49)))=k3_xboole_0(k4_xboole_0(A_48, B_49), B_49))), inference(superposition, [status(thm), theory('equality')], [c_284, c_2718])).
% 3.84/1.70  tff(c_2937, plain, (![A_116, B_117]: (k3_xboole_0(k4_xboole_0(A_116, B_117), B_117)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_8, c_2803])).
% 3.84/1.70  tff(c_18, plain, (![A_15, B_16, C_17]: (~r1_xboole_0(A_15, k3_xboole_0(B_16, C_17)) | ~r1_tarski(A_15, C_17) | r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.84/1.70  tff(c_2972, plain, (![A_15, B_117, A_116]: (~r1_xboole_0(A_15, k1_xboole_0) | ~r1_tarski(A_15, B_117) | r1_xboole_0(A_15, k4_xboole_0(A_116, B_117)))), inference(superposition, [status(thm), theory('equality')], [c_2937, c_18])).
% 3.84/1.70  tff(c_3419, plain, (![A_126, B_127, A_128]: (~r1_tarski(A_126, B_127) | r1_xboole_0(A_126, k4_xboole_0(A_128, B_127)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2972])).
% 3.84/1.70  tff(c_22, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.84/1.70  tff(c_3422, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_3419, c_22])).
% 3.84/1.70  tff(c_3465, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223, c_3422])).
% 3.84/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.70  
% 3.84/1.70  Inference rules
% 3.84/1.70  ----------------------
% 3.84/1.70  #Ref     : 0
% 3.84/1.70  #Sup     : 865
% 3.84/1.70  #Fact    : 0
% 3.84/1.70  #Define  : 0
% 3.84/1.70  #Split   : 0
% 3.84/1.70  #Chain   : 0
% 3.84/1.70  #Close   : 0
% 3.84/1.70  
% 3.84/1.70  Ordering : KBO
% 3.84/1.70  
% 3.84/1.70  Simplification rules
% 3.84/1.70  ----------------------
% 3.84/1.70  #Subsume      : 1
% 3.84/1.70  #Demod        : 827
% 3.84/1.70  #Tautology    : 574
% 3.84/1.70  #SimpNegUnit  : 0
% 3.84/1.70  #BackRed      : 4
% 3.84/1.70  
% 3.84/1.70  #Partial instantiations: 0
% 3.84/1.70  #Strategies tried      : 1
% 3.84/1.70  
% 3.84/1.70  Timing (in seconds)
% 3.84/1.70  ----------------------
% 3.84/1.70  Preprocessing        : 0.27
% 3.84/1.70  Parsing              : 0.15
% 3.84/1.70  CNF conversion       : 0.02
% 3.84/1.70  Main loop            : 0.66
% 3.84/1.70  Inferencing          : 0.21
% 3.84/1.70  Reduction            : 0.29
% 3.84/1.70  Demodulation         : 0.25
% 3.84/1.70  BG Simplification    : 0.03
% 3.84/1.70  Subsumption          : 0.09
% 3.84/1.70  Abstraction          : 0.04
% 3.84/1.70  MUC search           : 0.00
% 3.84/1.70  Cooper               : 0.00
% 3.84/1.71  Total                : 0.96
% 3.84/1.71  Index Insertion      : 0.00
% 3.84/1.71  Index Deletion       : 0.00
% 3.84/1.71  Index Matching       : 0.00
% 3.84/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
