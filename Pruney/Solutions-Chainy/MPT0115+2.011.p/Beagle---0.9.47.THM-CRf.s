%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:27 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   48 (  67 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   45 (  69 expanded)
%              Number of equality atoms :   28 (  44 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_197,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_246,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_197])).

tff(c_251,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_246])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_156,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_164,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_156])).

tff(c_229,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_197])).

tff(c_249,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_229])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45,plain,(
    ! [B_20,A_21] :
      ( r1_xboole_0(B_20,A_21)
      | ~ r1_xboole_0(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [B_13,A_12] : r1_xboole_0(B_13,k4_xboole_0(A_12,B_13)) ),
    inference(resolution,[status(thm)],[c_16,c_45])).

tff(c_67,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = A_26
      | ~ r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_80,plain,(
    ! [B_13,A_12] : k4_xboole_0(B_13,k4_xboole_0(A_12,B_13)) = B_13 ),
    inference(resolution,[status(thm)],[c_48,c_67])).

tff(c_344,plain,(
    ! [A_44,B_45,C_46] : k4_xboole_0(k3_xboole_0(A_44,B_45),C_46) = k3_xboole_0(A_44,k4_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_417,plain,(
    ! [C_47] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_47)) = k4_xboole_0('#skF_1',C_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_344])).

tff(c_438,plain,(
    ! [A_12] : k4_xboole_0('#skF_1',k4_xboole_0(A_12,'#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_417])).

tff(c_448,plain,(
    ! [A_48] : k4_xboole_0('#skF_1',k4_xboole_0(A_48,'#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_438])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_453,plain,(
    ! [A_48] : k3_xboole_0('#skF_1',k4_xboole_0(A_48,'#skF_2')) = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_12])).

tff(c_486,plain,(
    ! [A_48] : k3_xboole_0('#skF_1',k4_xboole_0(A_48,'#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_453])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k3_xboole_0(A_9,B_10),C_11) = k3_xboole_0(A_9,k4_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_151,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | k4_xboole_0(A_31,B_32) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_155,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_151,c_22])).

tff(c_343,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_155])).

tff(c_544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_343])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.29  
% 1.97/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.29  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.97/1.29  
% 1.97/1.29  %Foreground sorts:
% 1.97/1.29  
% 1.97/1.29  
% 1.97/1.29  %Background operators:
% 1.97/1.29  
% 1.97/1.29  
% 1.97/1.29  %Foreground operators:
% 1.97/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.97/1.29  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.29  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.29  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.29  
% 1.97/1.30  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.97/1.30  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.97/1.30  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.97/1.30  tff(f_52, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 1.97/1.30  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.97/1.30  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.97/1.30  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.97/1.30  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.97/1.30  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 1.97/1.30  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.97/1.30  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.30  tff(c_197, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.97/1.30  tff(c_246, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_197])).
% 1.97/1.30  tff(c_251, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_246])).
% 1.97/1.30  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.97/1.30  tff(c_156, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.97/1.30  tff(c_164, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_156])).
% 1.97/1.30  tff(c_229, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_164, c_197])).
% 1.97/1.30  tff(c_249, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_229])).
% 1.97/1.30  tff(c_16, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.97/1.30  tff(c_45, plain, (![B_20, A_21]: (r1_xboole_0(B_20, A_21) | ~r1_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.30  tff(c_48, plain, (![B_13, A_12]: (r1_xboole_0(B_13, k4_xboole_0(A_12, B_13)))), inference(resolution, [status(thm)], [c_16, c_45])).
% 1.97/1.30  tff(c_67, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=A_26 | ~r1_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.97/1.30  tff(c_80, plain, (![B_13, A_12]: (k4_xboole_0(B_13, k4_xboole_0(A_12, B_13))=B_13)), inference(resolution, [status(thm)], [c_48, c_67])).
% 1.97/1.30  tff(c_344, plain, (![A_44, B_45, C_46]: (k4_xboole_0(k3_xboole_0(A_44, B_45), C_46)=k3_xboole_0(A_44, k4_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.97/1.30  tff(c_417, plain, (![C_47]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_47))=k4_xboole_0('#skF_1', C_47))), inference(superposition, [status(thm), theory('equality')], [c_249, c_344])).
% 1.97/1.30  tff(c_438, plain, (![A_12]: (k4_xboole_0('#skF_1', k4_xboole_0(A_12, '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_417])).
% 1.97/1.30  tff(c_448, plain, (![A_48]: (k4_xboole_0('#skF_1', k4_xboole_0(A_48, '#skF_2'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_438])).
% 1.97/1.30  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.97/1.30  tff(c_453, plain, (![A_48]: (k3_xboole_0('#skF_1', k4_xboole_0(A_48, '#skF_2'))=k4_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_448, c_12])).
% 1.97/1.30  tff(c_486, plain, (![A_48]: (k3_xboole_0('#skF_1', k4_xboole_0(A_48, '#skF_2'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_251, c_453])).
% 1.97/1.30  tff(c_14, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k3_xboole_0(A_9, B_10), C_11)=k3_xboole_0(A_9, k4_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.97/1.30  tff(c_151, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | k4_xboole_0(A_31, B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.97/1.30  tff(c_22, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.97/1.30  tff(c_155, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_151, c_22])).
% 1.97/1.30  tff(c_343, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_155])).
% 1.97/1.30  tff(c_544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_486, c_343])).
% 1.97/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.30  
% 1.97/1.30  Inference rules
% 1.97/1.30  ----------------------
% 1.97/1.30  #Ref     : 0
% 1.97/1.30  #Sup     : 128
% 1.97/1.30  #Fact    : 0
% 1.97/1.30  #Define  : 0
% 1.97/1.30  #Split   : 0
% 1.97/1.30  #Chain   : 0
% 1.97/1.30  #Close   : 0
% 1.97/1.30  
% 1.97/1.30  Ordering : KBO
% 1.97/1.30  
% 1.97/1.30  Simplification rules
% 1.97/1.30  ----------------------
% 1.97/1.30  #Subsume      : 1
% 1.97/1.30  #Demod        : 55
% 1.97/1.30  #Tautology    : 82
% 1.97/1.30  #SimpNegUnit  : 0
% 1.97/1.30  #BackRed      : 2
% 1.97/1.30  
% 1.97/1.30  #Partial instantiations: 0
% 1.97/1.30  #Strategies tried      : 1
% 1.97/1.30  
% 1.97/1.30  Timing (in seconds)
% 1.97/1.30  ----------------------
% 1.97/1.31  Preprocessing        : 0.27
% 1.97/1.31  Parsing              : 0.14
% 1.97/1.31  CNF conversion       : 0.01
% 1.97/1.31  Main loop            : 0.22
% 1.97/1.31  Inferencing          : 0.09
% 1.97/1.31  Reduction            : 0.07
% 1.97/1.31  Demodulation         : 0.05
% 1.97/1.31  BG Simplification    : 0.01
% 1.97/1.31  Subsumption          : 0.03
% 1.97/1.31  Abstraction          : 0.01
% 1.97/1.31  MUC search           : 0.00
% 1.97/1.31  Cooper               : 0.00
% 1.97/1.31  Total                : 0.52
% 1.97/1.31  Index Insertion      : 0.00
% 1.97/1.31  Index Deletion       : 0.00
% 1.97/1.31  Index Matching       : 0.00
% 1.97/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
