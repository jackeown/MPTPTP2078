%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:49 EST 2020

% Result     : Theorem 5.03s
% Output     : CNFRefutation 5.03s
% Verified   : 
% Statistics : Number of formulae       :   45 (  70 expanded)
%              Number of leaves         :   17 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   39 (  68 expanded)
%              Number of equality atoms :   28 (  52 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k4_xboole_0(A,B),C)
       => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_129,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | k4_xboole_0(A_21,B_22) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).

tff(c_133,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_129,c_19])).

tff(c_371,plain,(
    ! [A_35,B_36,C_37] : k2_xboole_0(k2_xboole_0(A_35,B_36),C_37) = k2_xboole_0(A_35,k2_xboole_0(B_36,C_37)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_397,plain,(
    ! [C_37,A_35,B_36] : k2_xboole_0(C_37,k2_xboole_0(A_35,B_36)) = k2_xboole_0(A_35,k2_xboole_0(B_36,C_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_2])).

tff(c_34,plain,(
    ! [B_17,A_18] : k2_xboole_0(B_17,A_18) = k2_xboole_0(A_18,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ! [A_18] : k2_xboole_0(k1_xboole_0,A_18) = A_18 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1141,plain,(
    ! [C_58,A_59,B_60] : k2_xboole_0(C_58,k2_xboole_0(A_59,B_60)) = k2_xboole_0(A_59,k2_xboole_0(B_60,C_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_2])).

tff(c_1614,plain,(
    ! [A_64,C_65] : k2_xboole_0(k1_xboole_0,k2_xboole_0(A_64,C_65)) = k2_xboole_0(C_65,A_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1141])).

tff(c_1724,plain,(
    ! [B_7,A_6] : k2_xboole_0(k4_xboole_0(B_7,A_6),A_6) = k2_xboole_0(k1_xboole_0,k2_xboole_0(A_6,B_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1614])).

tff(c_4244,plain,(
    ! [B_88,A_89] : k2_xboole_0(k4_xboole_0(B_88,A_89),A_89) = k2_xboole_0(A_89,B_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1724])).

tff(c_18,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_154,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_178,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_154])).

tff(c_205,plain,(
    ! [A_29,B_30] : k2_xboole_0(A_29,k4_xboole_0(B_30,A_29)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_224,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_205])).

tff(c_239,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_224])).

tff(c_413,plain,(
    ! [C_37] : k2_xboole_0('#skF_3',k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),C_37)) = k2_xboole_0('#skF_3',C_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_371])).

tff(c_4355,plain,(
    k2_xboole_0('#skF_3',k2_xboole_0('#skF_2','#skF_1')) = k2_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4244,c_413])).

tff(c_4457,plain,(
    k2_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k2_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_397,c_2,c_4355])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_177,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_154])).

tff(c_5084,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4457,c_177])).

tff(c_5115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_5084])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:42:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.03/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.03/1.93  
% 5.03/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.03/1.93  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.03/1.93  
% 5.03/1.93  %Foreground sorts:
% 5.03/1.93  
% 5.03/1.93  
% 5.03/1.93  %Background operators:
% 5.03/1.93  
% 5.03/1.93  
% 5.03/1.93  %Foreground operators:
% 5.03/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.03/1.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.03/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.03/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.03/1.93  tff('#skF_2', type, '#skF_2': $i).
% 5.03/1.93  tff('#skF_3', type, '#skF_3': $i).
% 5.03/1.93  tff('#skF_1', type, '#skF_1': $i).
% 5.03/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.03/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.03/1.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.03/1.93  
% 5.03/1.94  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 5.03/1.94  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.03/1.94  tff(f_44, negated_conjecture, ~(![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 5.03/1.94  tff(f_37, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 5.03/1.94  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.03/1.94  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.03/1.94  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.03/1.94  tff(c_129, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | k4_xboole_0(A_21, B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.03/1.94  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.03/1.94  tff(c_16, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.03/1.94  tff(c_19, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 5.03/1.94  tff(c_133, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_129, c_19])).
% 5.03/1.94  tff(c_371, plain, (![A_35, B_36, C_37]: (k2_xboole_0(k2_xboole_0(A_35, B_36), C_37)=k2_xboole_0(A_35, k2_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.03/1.94  tff(c_397, plain, (![C_37, A_35, B_36]: (k2_xboole_0(C_37, k2_xboole_0(A_35, B_36))=k2_xboole_0(A_35, k2_xboole_0(B_36, C_37)))), inference(superposition, [status(thm), theory('equality')], [c_371, c_2])).
% 5.03/1.94  tff(c_34, plain, (![B_17, A_18]: (k2_xboole_0(B_17, A_18)=k2_xboole_0(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.03/1.94  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.03/1.94  tff(c_56, plain, (![A_18]: (k2_xboole_0(k1_xboole_0, A_18)=A_18)), inference(superposition, [status(thm), theory('equality')], [c_34, c_4])).
% 5.03/1.94  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.03/1.94  tff(c_1141, plain, (![C_58, A_59, B_60]: (k2_xboole_0(C_58, k2_xboole_0(A_59, B_60))=k2_xboole_0(A_59, k2_xboole_0(B_60, C_58)))), inference(superposition, [status(thm), theory('equality')], [c_371, c_2])).
% 5.03/1.94  tff(c_1614, plain, (![A_64, C_65]: (k2_xboole_0(k1_xboole_0, k2_xboole_0(A_64, C_65))=k2_xboole_0(C_65, A_64))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1141])).
% 5.03/1.94  tff(c_1724, plain, (![B_7, A_6]: (k2_xboole_0(k4_xboole_0(B_7, A_6), A_6)=k2_xboole_0(k1_xboole_0, k2_xboole_0(A_6, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1614])).
% 5.03/1.94  tff(c_4244, plain, (![B_88, A_89]: (k2_xboole_0(k4_xboole_0(B_88, A_89), A_89)=k2_xboole_0(A_89, B_88))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1724])).
% 5.03/1.94  tff(c_18, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.03/1.94  tff(c_154, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.03/1.94  tff(c_178, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_154])).
% 5.03/1.94  tff(c_205, plain, (![A_29, B_30]: (k2_xboole_0(A_29, k4_xboole_0(B_30, A_29))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.03/1.94  tff(c_224, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_178, c_205])).
% 5.03/1.94  tff(c_239, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_224])).
% 5.03/1.94  tff(c_413, plain, (![C_37]: (k2_xboole_0('#skF_3', k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), C_37))=k2_xboole_0('#skF_3', C_37))), inference(superposition, [status(thm), theory('equality')], [c_239, c_371])).
% 5.03/1.94  tff(c_4355, plain, (k2_xboole_0('#skF_3', k2_xboole_0('#skF_2', '#skF_1'))=k2_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4244, c_413])).
% 5.03/1.94  tff(c_4457, plain, (k2_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k2_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_397, c_2, c_4355])).
% 5.03/1.94  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.03/1.94  tff(c_177, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_154])).
% 5.03/1.94  tff(c_5084, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4457, c_177])).
% 5.03/1.94  tff(c_5115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_5084])).
% 5.03/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.03/1.94  
% 5.03/1.94  Inference rules
% 5.03/1.94  ----------------------
% 5.03/1.94  #Ref     : 0
% 5.03/1.94  #Sup     : 1281
% 5.03/1.94  #Fact    : 0
% 5.03/1.94  #Define  : 0
% 5.03/1.94  #Split   : 0
% 5.03/1.94  #Chain   : 0
% 5.03/1.94  #Close   : 0
% 5.03/1.94  
% 5.03/1.94  Ordering : KBO
% 5.03/1.94  
% 5.03/1.94  Simplification rules
% 5.03/1.94  ----------------------
% 5.03/1.94  #Subsume      : 44
% 5.03/1.94  #Demod        : 1266
% 5.03/1.94  #Tautology    : 759
% 5.03/1.94  #SimpNegUnit  : 1
% 5.03/1.94  #BackRed      : 0
% 5.03/1.94  
% 5.03/1.94  #Partial instantiations: 0
% 5.03/1.94  #Strategies tried      : 1
% 5.03/1.94  
% 5.03/1.94  Timing (in seconds)
% 5.03/1.94  ----------------------
% 5.03/1.95  Preprocessing        : 0.27
% 5.03/1.95  Parsing              : 0.15
% 5.03/1.95  CNF conversion       : 0.02
% 5.03/1.95  Main loop            : 0.93
% 5.03/1.95  Inferencing          : 0.23
% 5.03/1.95  Reduction            : 0.50
% 5.03/1.95  Demodulation         : 0.44
% 5.03/1.95  BG Simplification    : 0.03
% 5.03/1.95  Subsumption          : 0.12
% 5.03/1.95  Abstraction          : 0.04
% 5.03/1.95  MUC search           : 0.00
% 5.03/1.95  Cooper               : 0.00
% 5.03/1.95  Total                : 1.23
% 5.03/1.95  Index Insertion      : 0.00
% 5.03/1.95  Index Deletion       : 0.00
% 5.03/1.95  Index Matching       : 0.00
% 5.03/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
