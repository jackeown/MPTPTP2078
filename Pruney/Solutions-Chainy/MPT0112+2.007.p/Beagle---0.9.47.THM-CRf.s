%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:09 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 119 expanded)
%              Number of leaves         :   19 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :   44 ( 132 expanded)
%              Number of equality atoms :   32 (  95 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_42,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_xboole_0(A,B)
          & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_6,plain,(
    ! [B_4] : ~ r2_xboole_0(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_56,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ r2_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_56])).

tff(c_99,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_103,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_60,c_99])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_123,plain,(
    ! [A_29,B_30] : k5_xboole_0(A_29,k3_xboole_0(A_29,B_30)) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_198,plain,(
    ! [B_34,A_35] : k5_xboole_0(B_34,k3_xboole_0(A_35,B_34)) = k4_xboole_0(B_34,A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_123])).

tff(c_226,plain,(
    k5_xboole_0('#skF_2','#skF_1') = k4_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_198])).

tff(c_237,plain,(
    k5_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_226])).

tff(c_18,plain,(
    ! [A_12,B_13,C_14] : k5_xboole_0(k5_xboole_0(A_12,B_13),C_14) = k5_xboole_0(A_12,k5_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_251,plain,(
    ! [C_38] : k5_xboole_0('#skF_2',k5_xboole_0('#skF_1',C_38)) = k5_xboole_0(k1_xboole_0,C_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_18])).

tff(c_276,plain,(
    k5_xboole_0(k1_xboole_0,'#skF_1') = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_251])).

tff(c_281,plain,(
    k5_xboole_0(k1_xboole_0,'#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_276])).

tff(c_146,plain,(
    ! [A_31,B_32,C_33] : k5_xboole_0(k5_xboole_0(A_31,B_32),C_33) = k5_xboole_0(A_31,k5_xboole_0(B_32,C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_290,plain,(
    ! [A_39,B_40] : k5_xboole_0(A_39,k5_xboole_0(B_40,k5_xboole_0(A_39,B_40))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_146])).

tff(c_369,plain,(
    ! [A_41] : k5_xboole_0(A_41,k5_xboole_0(k1_xboole_0,A_41)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_290])).

tff(c_243,plain,(
    ! [C_14] : k5_xboole_0('#skF_2',k5_xboole_0('#skF_1',C_14)) = k5_xboole_0(k1_xboole_0,C_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_18])).

tff(c_385,plain,(
    k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,'#skF_1')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_243])).

tff(c_430,plain,(
    k5_xboole_0(k1_xboole_0,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_14,c_385])).

tff(c_405,plain,(
    k5_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_369])).

tff(c_796,plain,(
    ! [A_47,C_48] : k5_xboole_0(A_47,k5_xboole_0(A_47,C_48)) = k5_xboole_0(k1_xboole_0,C_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_146])).

tff(c_869,plain,(
    k5_xboole_0(k1_xboole_0,'#skF_2') = k5_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_796])).

tff(c_935,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_14,c_869])).

tff(c_1078,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_24])).

tff(c_1083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_1078])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:00:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.41  
% 2.77/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.41  %$ r2_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.77/1.41  
% 2.77/1.41  %Foreground sorts:
% 2.77/1.41  
% 2.77/1.41  
% 2.77/1.41  %Background operators:
% 2.77/1.41  
% 2.77/1.41  
% 2.77/1.41  %Foreground operators:
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.77/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.77/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.77/1.41  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.77/1.41  
% 2.77/1.42  tff(f_34, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.77/1.42  tff(f_42, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.77/1.42  tff(f_51, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.77/1.42  tff(f_57, negated_conjecture, ~(![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_xboole_1)).
% 2.77/1.42  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.77/1.42  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.77/1.42  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.77/1.42  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.77/1.42  tff(c_6, plain, (![B_4]: (~r2_xboole_0(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.77/1.42  tff(c_14, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.77/1.42  tff(c_20, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.77/1.42  tff(c_22, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.77/1.42  tff(c_24, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.77/1.42  tff(c_56, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~r2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.77/1.42  tff(c_60, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_56])).
% 2.77/1.42  tff(c_99, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.77/1.42  tff(c_103, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_60, c_99])).
% 2.77/1.42  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.77/1.42  tff(c_123, plain, (![A_29, B_30]: (k5_xboole_0(A_29, k3_xboole_0(A_29, B_30))=k4_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.77/1.42  tff(c_198, plain, (![B_34, A_35]: (k5_xboole_0(B_34, k3_xboole_0(A_35, B_34))=k4_xboole_0(B_34, A_35))), inference(superposition, [status(thm), theory('equality')], [c_2, c_123])).
% 2.77/1.42  tff(c_226, plain, (k5_xboole_0('#skF_2', '#skF_1')=k4_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_103, c_198])).
% 2.77/1.42  tff(c_237, plain, (k5_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_226])).
% 2.77/1.42  tff(c_18, plain, (![A_12, B_13, C_14]: (k5_xboole_0(k5_xboole_0(A_12, B_13), C_14)=k5_xboole_0(A_12, k5_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.77/1.42  tff(c_251, plain, (![C_38]: (k5_xboole_0('#skF_2', k5_xboole_0('#skF_1', C_38))=k5_xboole_0(k1_xboole_0, C_38))), inference(superposition, [status(thm), theory('equality')], [c_237, c_18])).
% 2.77/1.42  tff(c_276, plain, (k5_xboole_0(k1_xboole_0, '#skF_1')=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_251])).
% 2.77/1.42  tff(c_281, plain, (k5_xboole_0(k1_xboole_0, '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_276])).
% 2.77/1.42  tff(c_146, plain, (![A_31, B_32, C_33]: (k5_xboole_0(k5_xboole_0(A_31, B_32), C_33)=k5_xboole_0(A_31, k5_xboole_0(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.77/1.42  tff(c_290, plain, (![A_39, B_40]: (k5_xboole_0(A_39, k5_xboole_0(B_40, k5_xboole_0(A_39, B_40)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_146])).
% 2.77/1.42  tff(c_369, plain, (![A_41]: (k5_xboole_0(A_41, k5_xboole_0(k1_xboole_0, A_41))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_290])).
% 2.77/1.42  tff(c_243, plain, (![C_14]: (k5_xboole_0('#skF_2', k5_xboole_0('#skF_1', C_14))=k5_xboole_0(k1_xboole_0, C_14))), inference(superposition, [status(thm), theory('equality')], [c_237, c_18])).
% 2.77/1.42  tff(c_385, plain, (k5_xboole_0(k1_xboole_0, k5_xboole_0(k1_xboole_0, '#skF_1'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_369, c_243])).
% 2.77/1.42  tff(c_430, plain, (k5_xboole_0(k1_xboole_0, '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_281, c_14, c_385])).
% 2.77/1.42  tff(c_405, plain, (k5_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_281, c_369])).
% 2.77/1.42  tff(c_796, plain, (![A_47, C_48]: (k5_xboole_0(A_47, k5_xboole_0(A_47, C_48))=k5_xboole_0(k1_xboole_0, C_48))), inference(superposition, [status(thm), theory('equality')], [c_20, c_146])).
% 2.77/1.42  tff(c_869, plain, (k5_xboole_0(k1_xboole_0, '#skF_2')=k5_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_405, c_796])).
% 2.77/1.42  tff(c_935, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_430, c_14, c_869])).
% 2.77/1.42  tff(c_1078, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_935, c_24])).
% 2.77/1.42  tff(c_1083, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_1078])).
% 2.77/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.42  
% 2.77/1.42  Inference rules
% 2.77/1.42  ----------------------
% 2.77/1.42  #Ref     : 0
% 2.77/1.42  #Sup     : 251
% 2.77/1.42  #Fact    : 0
% 2.77/1.42  #Define  : 0
% 2.77/1.42  #Split   : 0
% 2.77/1.42  #Chain   : 0
% 2.77/1.42  #Close   : 0
% 2.77/1.42  
% 2.77/1.42  Ordering : KBO
% 2.77/1.42  
% 2.77/1.42  Simplification rules
% 2.77/1.42  ----------------------
% 2.77/1.42  #Subsume      : 1
% 2.77/1.42  #Demod        : 235
% 2.77/1.42  #Tautology    : 165
% 2.77/1.42  #SimpNegUnit  : 1
% 2.77/1.42  #BackRed      : 12
% 2.77/1.42  
% 2.77/1.42  #Partial instantiations: 0
% 2.77/1.42  #Strategies tried      : 1
% 2.77/1.42  
% 2.77/1.42  Timing (in seconds)
% 2.77/1.42  ----------------------
% 2.77/1.42  Preprocessing        : 0.26
% 2.77/1.42  Parsing              : 0.14
% 2.77/1.42  CNF conversion       : 0.02
% 2.77/1.42  Main loop            : 0.37
% 2.77/1.42  Inferencing          : 0.13
% 2.77/1.42  Reduction            : 0.14
% 2.77/1.42  Demodulation         : 0.12
% 2.77/1.42  BG Simplification    : 0.02
% 2.77/1.42  Subsumption          : 0.05
% 2.77/1.42  Abstraction          : 0.02
% 2.77/1.42  MUC search           : 0.00
% 2.77/1.42  Cooper               : 0.00
% 2.77/1.42  Total                : 0.65
% 2.77/1.42  Index Insertion      : 0.00
% 2.77/1.42  Index Deletion       : 0.00
% 2.77/1.43  Index Matching       : 0.00
% 2.77/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
