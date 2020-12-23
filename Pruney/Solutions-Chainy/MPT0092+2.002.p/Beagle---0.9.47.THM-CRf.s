%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:29 EST 2020

% Result     : Theorem 6.85s
% Output     : CNFRefutation 6.92s
% Verified   : 
% Statistics : Number of formulae       :   60 (  95 expanded)
%              Number of leaves         :   22 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 (  96 expanded)
%              Number of equality atoms :   40 (  71 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_87,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_87])).

tff(c_334,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_375,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_334])).

tff(c_385,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_375])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_417,plain,(
    ! [A_49,B_50] : k4_xboole_0(k2_xboole_0(A_49,B_50),B_50) = k4_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_436,plain,(
    ! [A_49] : k4_xboole_0(A_49,k1_xboole_0) = k2_xboole_0(A_49,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_12])).

tff(c_484,plain,(
    ! [A_51] : k2_xboole_0(A_51,k1_xboole_0) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_436])).

tff(c_503,plain,(
    ! [A_1] : k2_xboole_0(k1_xboole_0,A_1) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_484])).

tff(c_38,plain,(
    ! [A_23,B_24] : r1_tarski(k4_xboole_0(A_23,B_24),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41,plain,(
    ! [A_9] : r1_tarski(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_38])).

tff(c_101,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_41,c_87])).

tff(c_20,plain,(
    ! [A_17,B_18,C_19] : k4_xboole_0(k3_xboole_0(A_17,B_18),C_19) = k3_xboole_0(A_17,k4_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_574,plain,(
    ! [A_53,B_54,C_55] : k4_xboole_0(k4_xboole_0(A_53,B_54),C_55) = k4_xboole_0(A_53,k2_xboole_0(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_620,plain,(
    ! [A_15,B_16,C_55] : k4_xboole_0(A_15,k2_xboole_0(k4_xboole_0(A_15,B_16),C_55)) = k4_xboole_0(k3_xboole_0(A_15,B_16),C_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_574])).

tff(c_7711,plain,(
    ! [A_154,B_155,C_156] : k4_xboole_0(A_154,k2_xboole_0(k4_xboole_0(A_154,B_155),C_156)) = k3_xboole_0(A_154,k4_xboole_0(B_155,C_156)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_620])).

tff(c_7958,plain,(
    ! [A_9,C_156] : k4_xboole_0(A_9,k2_xboole_0(k1_xboole_0,C_156)) = k3_xboole_0(A_9,k4_xboole_0(A_9,C_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_7711])).

tff(c_8779,plain,(
    ! [A_164,C_165] : k3_xboole_0(A_164,k4_xboole_0(A_164,C_165)) = k4_xboole_0(A_164,C_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_7958])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_102,plain,(
    ! [A_5,B_6] : k4_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_87])).

tff(c_1012,plain,(
    ! [A_67,B_68] : k4_xboole_0(k3_xboole_0(A_67,B_68),A_67) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_102])).

tff(c_1042,plain,(
    ! [C_19,B_18] : k3_xboole_0(C_19,k4_xboole_0(B_18,C_19)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1012])).

tff(c_4069,plain,(
    ! [A_121,B_122] : k4_xboole_0(A_121,k3_xboole_0(A_121,B_122)) = k3_xboole_0(A_121,k4_xboole_0(A_121,B_122)) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_18])).

tff(c_4168,plain,(
    ! [C_19,B_18] : k3_xboole_0(C_19,k4_xboole_0(C_19,k4_xboole_0(B_18,C_19))) = k4_xboole_0(C_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1042,c_4069])).

tff(c_4217,plain,(
    ! [C_19,B_18] : k3_xboole_0(C_19,k4_xboole_0(C_19,k4_xboole_0(B_18,C_19))) = C_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4168])).

tff(c_9000,plain,(
    ! [A_166,B_167] : k4_xboole_0(A_166,k4_xboole_0(B_167,A_166)) = A_166 ),
    inference(superposition,[status(thm),theory(equality)],[c_8779,c_4217])).

tff(c_781,plain,(
    ! [A_59,B_60,C_61] : k4_xboole_0(k3_xboole_0(A_59,B_60),C_61) = k3_xboole_0(A_59,k4_xboole_0(B_60,C_61)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_826,plain,(
    ! [C_61] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_61)) = k4_xboole_0('#skF_1',C_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_781])).

tff(c_9067,plain,(
    ! [B_167] : k4_xboole_0('#skF_1',k4_xboole_0(B_167,'#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9000,c_826])).

tff(c_9229,plain,(
    ! [B_167] : k4_xboole_0('#skF_1',k4_xboole_0(B_167,'#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_9067])).

tff(c_76,plain,(
    ! [A_28,B_29] :
      ( r1_xboole_0(A_28,B_29)
      | k4_xboole_0(A_28,B_29) != A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_80,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_76,c_26])).

tff(c_11104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9229,c_80])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n025.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 21:07:06 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.85/2.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.85/2.50  
% 6.85/2.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.85/2.51  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.85/2.51  
% 6.85/2.51  %Foreground sorts:
% 6.85/2.51  
% 6.85/2.51  
% 6.85/2.51  %Background operators:
% 6.85/2.51  
% 6.85/2.51  
% 6.85/2.51  %Foreground operators:
% 6.85/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.85/2.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.85/2.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.85/2.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.85/2.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.85/2.51  tff('#skF_2', type, '#skF_2': $i).
% 6.85/2.51  tff('#skF_3', type, '#skF_3': $i).
% 6.85/2.51  tff('#skF_1', type, '#skF_1': $i).
% 6.85/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.85/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.85/2.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.85/2.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.85/2.51  
% 6.92/2.52  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 6.92/2.52  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 6.92/2.52  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.92/2.52  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.92/2.52  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.92/2.52  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 6.92/2.52  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.92/2.52  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 6.92/2.52  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 6.92/2.52  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.92/2.52  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.92/2.52  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.92/2.52  tff(c_87, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.92/2.52  tff(c_103, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_87])).
% 6.92/2.52  tff(c_334, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.92/2.52  tff(c_375, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_103, c_334])).
% 6.92/2.52  tff(c_385, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_375])).
% 6.92/2.52  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.92/2.52  tff(c_417, plain, (![A_49, B_50]: (k4_xboole_0(k2_xboole_0(A_49, B_50), B_50)=k4_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.92/2.52  tff(c_436, plain, (![A_49]: (k4_xboole_0(A_49, k1_xboole_0)=k2_xboole_0(A_49, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_417, c_12])).
% 6.92/2.52  tff(c_484, plain, (![A_51]: (k2_xboole_0(A_51, k1_xboole_0)=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_436])).
% 6.92/2.52  tff(c_503, plain, (![A_1]: (k2_xboole_0(k1_xboole_0, A_1)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_484])).
% 6.92/2.52  tff(c_38, plain, (![A_23, B_24]: (r1_tarski(k4_xboole_0(A_23, B_24), A_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.92/2.52  tff(c_41, plain, (![A_9]: (r1_tarski(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_12, c_38])).
% 6.92/2.52  tff(c_101, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_41, c_87])).
% 6.92/2.52  tff(c_20, plain, (![A_17, B_18, C_19]: (k4_xboole_0(k3_xboole_0(A_17, B_18), C_19)=k3_xboole_0(A_17, k4_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.92/2.52  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.92/2.52  tff(c_574, plain, (![A_53, B_54, C_55]: (k4_xboole_0(k4_xboole_0(A_53, B_54), C_55)=k4_xboole_0(A_53, k2_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.92/2.52  tff(c_620, plain, (![A_15, B_16, C_55]: (k4_xboole_0(A_15, k2_xboole_0(k4_xboole_0(A_15, B_16), C_55))=k4_xboole_0(k3_xboole_0(A_15, B_16), C_55))), inference(superposition, [status(thm), theory('equality')], [c_18, c_574])).
% 6.92/2.52  tff(c_7711, plain, (![A_154, B_155, C_156]: (k4_xboole_0(A_154, k2_xboole_0(k4_xboole_0(A_154, B_155), C_156))=k3_xboole_0(A_154, k4_xboole_0(B_155, C_156)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_620])).
% 6.92/2.52  tff(c_7958, plain, (![A_9, C_156]: (k4_xboole_0(A_9, k2_xboole_0(k1_xboole_0, C_156))=k3_xboole_0(A_9, k4_xboole_0(A_9, C_156)))), inference(superposition, [status(thm), theory('equality')], [c_101, c_7711])).
% 6.92/2.52  tff(c_8779, plain, (![A_164, C_165]: (k3_xboole_0(A_164, k4_xboole_0(A_164, C_165))=k4_xboole_0(A_164, C_165))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_7958])).
% 6.92/2.52  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.92/2.52  tff(c_102, plain, (![A_5, B_6]: (k4_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_87])).
% 6.92/2.52  tff(c_1012, plain, (![A_67, B_68]: (k4_xboole_0(k3_xboole_0(A_67, B_68), A_67)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_334, c_102])).
% 6.92/2.52  tff(c_1042, plain, (![C_19, B_18]: (k3_xboole_0(C_19, k4_xboole_0(B_18, C_19))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_1012])).
% 6.92/2.52  tff(c_4069, plain, (![A_121, B_122]: (k4_xboole_0(A_121, k3_xboole_0(A_121, B_122))=k3_xboole_0(A_121, k4_xboole_0(A_121, B_122)))), inference(superposition, [status(thm), theory('equality')], [c_334, c_18])).
% 6.92/2.52  tff(c_4168, plain, (![C_19, B_18]: (k3_xboole_0(C_19, k4_xboole_0(C_19, k4_xboole_0(B_18, C_19)))=k4_xboole_0(C_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1042, c_4069])).
% 6.92/2.52  tff(c_4217, plain, (![C_19, B_18]: (k3_xboole_0(C_19, k4_xboole_0(C_19, k4_xboole_0(B_18, C_19)))=C_19)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4168])).
% 6.92/2.52  tff(c_9000, plain, (![A_166, B_167]: (k4_xboole_0(A_166, k4_xboole_0(B_167, A_166))=A_166)), inference(superposition, [status(thm), theory('equality')], [c_8779, c_4217])).
% 6.92/2.52  tff(c_781, plain, (![A_59, B_60, C_61]: (k4_xboole_0(k3_xboole_0(A_59, B_60), C_61)=k3_xboole_0(A_59, k4_xboole_0(B_60, C_61)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.92/2.52  tff(c_826, plain, (![C_61]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_61))=k4_xboole_0('#skF_1', C_61))), inference(superposition, [status(thm), theory('equality')], [c_385, c_781])).
% 6.92/2.52  tff(c_9067, plain, (![B_167]: (k4_xboole_0('#skF_1', k4_xboole_0(B_167, '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_9000, c_826])).
% 6.92/2.52  tff(c_9229, plain, (![B_167]: (k4_xboole_0('#skF_1', k4_xboole_0(B_167, '#skF_2'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_385, c_9067])).
% 6.92/2.52  tff(c_76, plain, (![A_28, B_29]: (r1_xboole_0(A_28, B_29) | k4_xboole_0(A_28, B_29)!=A_28)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.92/2.52  tff(c_26, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.92/2.52  tff(c_80, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))!='#skF_1'), inference(resolution, [status(thm)], [c_76, c_26])).
% 6.92/2.52  tff(c_11104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9229, c_80])).
% 6.92/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.92/2.52  
% 6.92/2.52  Inference rules
% 6.92/2.52  ----------------------
% 6.92/2.52  #Ref     : 0
% 6.92/2.52  #Sup     : 2743
% 6.92/2.52  #Fact    : 0
% 6.92/2.52  #Define  : 0
% 6.92/2.52  #Split   : 0
% 6.92/2.52  #Chain   : 0
% 6.92/2.52  #Close   : 0
% 6.92/2.52  
% 6.92/2.52  Ordering : KBO
% 6.92/2.52  
% 6.92/2.52  Simplification rules
% 6.92/2.52  ----------------------
% 6.92/2.52  #Subsume      : 23
% 6.92/2.52  #Demod        : 3179
% 6.92/2.52  #Tautology    : 1968
% 6.92/2.52  #SimpNegUnit  : 0
% 6.92/2.52  #BackRed      : 10
% 6.92/2.52  
% 6.92/2.52  #Partial instantiations: 0
% 6.92/2.52  #Strategies tried      : 1
% 6.92/2.52  
% 6.92/2.52  Timing (in seconds)
% 6.92/2.52  ----------------------
% 6.92/2.52  Preprocessing        : 0.30
% 6.92/2.52  Parsing              : 0.16
% 6.92/2.52  CNF conversion       : 0.02
% 6.92/2.52  Main loop            : 1.48
% 6.92/2.52  Inferencing          : 0.40
% 6.92/2.52  Reduction            : 0.77
% 6.92/2.52  Demodulation         : 0.66
% 6.92/2.52  BG Simplification    : 0.04
% 6.92/2.53  Subsumption          : 0.20
% 6.92/2.53  Abstraction          : 0.07
% 6.92/2.53  MUC search           : 0.00
% 6.92/2.53  Cooper               : 0.00
% 6.92/2.53  Total                : 1.82
% 6.92/2.53  Index Insertion      : 0.00
% 6.92/2.53  Index Deletion       : 0.00
% 6.92/2.53  Index Matching       : 0.00
% 6.92/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
