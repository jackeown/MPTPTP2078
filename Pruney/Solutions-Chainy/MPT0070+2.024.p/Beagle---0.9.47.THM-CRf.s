%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:21 EST 2020

% Result     : Theorem 8.59s
% Output     : CNFRefutation 8.59s
% Verified   : 
% Statistics : Number of formulae       :   59 (  84 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 (  88 expanded)
%              Number of equality atoms :   40 (  61 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(c_251,plain,(
    ! [A_36,B_37] :
      ( r1_xboole_0(A_36,B_37)
      | k3_xboole_0(A_36,B_37) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_259,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_251,c_24])).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_96,plain,(
    ! [A_8,B_9] : k4_xboole_0(k4_xboole_0(A_8,B_9),A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_85])).

tff(c_351,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_382,plain,(
    ! [A_8,B_9] : k4_xboole_0(k4_xboole_0(A_8,B_9),k1_xboole_0) = k3_xboole_0(k4_xboole_0(A_8,B_9),A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_351])).

tff(c_2747,plain,(
    ! [A_96,B_97] : k3_xboole_0(k4_xboole_0(A_96,B_97),A_96) = k4_xboole_0(A_96,B_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_382])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18405,plain,(
    ! [A_309,B_310] : k3_xboole_0(A_309,k4_xboole_0(A_309,B_310)) = k4_xboole_0(A_309,B_310) ),
    inference(superposition,[status(thm),theory(equality)],[c_2747,c_2])).

tff(c_26,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_223,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_227,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_223])).

tff(c_231,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_2])).

tff(c_22,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1560,plain,(
    ! [A_78,B_79] : k4_xboole_0(A_78,k3_xboole_0(A_78,B_79)) = k3_xboole_0(A_78,k4_xboole_0(A_78,B_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_22])).

tff(c_1620,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_1560])).

tff(c_1648,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1620])).

tff(c_18555,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_18405,c_1648])).

tff(c_494,plain,(
    ! [A_48,B_49,C_50] : k4_xboole_0(k4_xboole_0(A_48,B_49),C_50) = k4_xboole_0(A_48,k2_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_520,plain,(
    ! [C_50,B_49] : k4_xboole_0(C_50,k2_xboole_0(B_49,C_50)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_96])).

tff(c_16,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_97,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_85])).

tff(c_260,plain,(
    ! [A_38,B_39] : k2_xboole_0(A_38,k4_xboole_0(B_39,A_38)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_278,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_260])).

tff(c_287,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_278])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k4_xboole_0(A_13,B_14),C_15) = k4_xboole_0(A_13,k2_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_507,plain,(
    ! [A_48,B_49,B_17] : k4_xboole_0(A_48,k2_xboole_0(B_49,k4_xboole_0(k4_xboole_0(A_48,B_49),B_17))) = k3_xboole_0(k4_xboole_0(A_48,B_49),B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_22])).

tff(c_4521,plain,(
    ! [A_128,B_129,B_130] : k4_xboole_0(A_128,k2_xboole_0(B_129,k4_xboole_0(A_128,k2_xboole_0(B_129,B_130)))) = k3_xboole_0(k4_xboole_0(A_128,B_129),B_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_507])).

tff(c_4719,plain,(
    ! [A_128] : k4_xboole_0(A_128,k2_xboole_0('#skF_2',k4_xboole_0(A_128,'#skF_2'))) = k3_xboole_0(k4_xboole_0(A_128,'#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_4521])).

tff(c_4781,plain,(
    ! [A_128] : k3_xboole_0('#skF_1',k4_xboole_0(A_128,'#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_16,c_2,c_4719])).

tff(c_18863,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18555,c_4781])).

tff(c_18914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_18863])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:20:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.59/3.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.59/3.36  
% 8.59/3.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.59/3.36  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.59/3.36  
% 8.59/3.36  %Foreground sorts:
% 8.59/3.36  
% 8.59/3.36  
% 8.59/3.36  %Background operators:
% 8.59/3.36  
% 8.59/3.36  
% 8.59/3.36  %Foreground operators:
% 8.59/3.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.59/3.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.59/3.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.59/3.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.59/3.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.59/3.36  tff('#skF_2', type, '#skF_2': $i).
% 8.59/3.36  tff('#skF_3', type, '#skF_3': $i).
% 8.59/3.36  tff('#skF_1', type, '#skF_1': $i).
% 8.59/3.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.59/3.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.59/3.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.59/3.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.59/3.36  
% 8.59/3.37  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.59/3.37  tff(f_54, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 8.59/3.37  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.59/3.37  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.59/3.37  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.59/3.37  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.59/3.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.59/3.37  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.59/3.37  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.59/3.37  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 8.59/3.37  tff(c_251, plain, (![A_36, B_37]: (r1_xboole_0(A_36, B_37) | k3_xboole_0(A_36, B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.59/3.37  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.59/3.37  tff(c_259, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_251, c_24])).
% 8.59/3.37  tff(c_18, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.59/3.37  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.59/3.37  tff(c_85, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.59/3.37  tff(c_96, plain, (![A_8, B_9]: (k4_xboole_0(k4_xboole_0(A_8, B_9), A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_85])).
% 8.59/3.37  tff(c_351, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.59/3.37  tff(c_382, plain, (![A_8, B_9]: (k4_xboole_0(k4_xboole_0(A_8, B_9), k1_xboole_0)=k3_xboole_0(k4_xboole_0(A_8, B_9), A_8))), inference(superposition, [status(thm), theory('equality')], [c_96, c_351])).
% 8.59/3.37  tff(c_2747, plain, (![A_96, B_97]: (k3_xboole_0(k4_xboole_0(A_96, B_97), A_96)=k4_xboole_0(A_96, B_97))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_382])).
% 8.59/3.37  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.59/3.37  tff(c_18405, plain, (![A_309, B_310]: (k3_xboole_0(A_309, k4_xboole_0(A_309, B_310))=k4_xboole_0(A_309, B_310))), inference(superposition, [status(thm), theory('equality')], [c_2747, c_2])).
% 8.59/3.37  tff(c_26, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.59/3.37  tff(c_223, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.59/3.37  tff(c_227, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_223])).
% 8.59/3.37  tff(c_231, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_227, c_2])).
% 8.59/3.37  tff(c_22, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.59/3.37  tff(c_1560, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k3_xboole_0(A_78, B_79))=k3_xboole_0(A_78, k4_xboole_0(A_78, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_351, c_22])).
% 8.59/3.37  tff(c_1620, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_231, c_1560])).
% 8.59/3.37  tff(c_1648, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1620])).
% 8.59/3.37  tff(c_18555, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_18405, c_1648])).
% 8.59/3.37  tff(c_494, plain, (![A_48, B_49, C_50]: (k4_xboole_0(k4_xboole_0(A_48, B_49), C_50)=k4_xboole_0(A_48, k2_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.59/3.37  tff(c_520, plain, (![C_50, B_49]: (k4_xboole_0(C_50, k2_xboole_0(B_49, C_50))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_494, c_96])).
% 8.59/3.37  tff(c_16, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.59/3.37  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.59/3.37  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.59/3.37  tff(c_97, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_85])).
% 8.59/3.37  tff(c_260, plain, (![A_38, B_39]: (k2_xboole_0(A_38, k4_xboole_0(B_39, A_38))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.59/3.37  tff(c_278, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_97, c_260])).
% 8.59/3.37  tff(c_287, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_278])).
% 8.59/3.37  tff(c_20, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k4_xboole_0(A_13, B_14), C_15)=k4_xboole_0(A_13, k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.59/3.37  tff(c_507, plain, (![A_48, B_49, B_17]: (k4_xboole_0(A_48, k2_xboole_0(B_49, k4_xboole_0(k4_xboole_0(A_48, B_49), B_17)))=k3_xboole_0(k4_xboole_0(A_48, B_49), B_17))), inference(superposition, [status(thm), theory('equality')], [c_494, c_22])).
% 8.59/3.37  tff(c_4521, plain, (![A_128, B_129, B_130]: (k4_xboole_0(A_128, k2_xboole_0(B_129, k4_xboole_0(A_128, k2_xboole_0(B_129, B_130))))=k3_xboole_0(k4_xboole_0(A_128, B_129), B_130))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_507])).
% 8.59/3.37  tff(c_4719, plain, (![A_128]: (k4_xboole_0(A_128, k2_xboole_0('#skF_2', k4_xboole_0(A_128, '#skF_2')))=k3_xboole_0(k4_xboole_0(A_128, '#skF_2'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_287, c_4521])).
% 8.59/3.37  tff(c_4781, plain, (![A_128]: (k3_xboole_0('#skF_1', k4_xboole_0(A_128, '#skF_2'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_520, c_16, c_2, c_4719])).
% 8.59/3.37  tff(c_18863, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_18555, c_4781])).
% 8.59/3.37  tff(c_18914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_259, c_18863])).
% 8.59/3.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.59/3.37  
% 8.59/3.37  Inference rules
% 8.59/3.37  ----------------------
% 8.59/3.37  #Ref     : 0
% 8.59/3.37  #Sup     : 4585
% 8.59/3.37  #Fact    : 0
% 8.59/3.37  #Define  : 0
% 8.59/3.37  #Split   : 0
% 8.59/3.37  #Chain   : 0
% 8.59/3.37  #Close   : 0
% 8.59/3.37  
% 8.59/3.37  Ordering : KBO
% 8.59/3.37  
% 8.59/3.37  Simplification rules
% 8.59/3.37  ----------------------
% 8.59/3.37  #Subsume      : 0
% 8.59/3.37  #Demod        : 5252
% 8.59/3.37  #Tautology    : 3354
% 8.59/3.37  #SimpNegUnit  : 1
% 8.59/3.37  #BackRed      : 18
% 8.59/3.37  
% 8.59/3.37  #Partial instantiations: 0
% 8.59/3.37  #Strategies tried      : 1
% 8.59/3.37  
% 8.59/3.37  Timing (in seconds)
% 8.59/3.37  ----------------------
% 8.59/3.37  Preprocessing        : 0.27
% 8.59/3.37  Parsing              : 0.15
% 8.59/3.37  CNF conversion       : 0.02
% 8.59/3.37  Main loop            : 2.33
% 8.59/3.37  Inferencing          : 0.52
% 8.59/3.37  Reduction            : 1.26
% 8.59/3.37  Demodulation         : 1.10
% 8.59/3.37  BG Simplification    : 0.06
% 8.59/3.37  Subsumption          : 0.37
% 8.59/3.37  Abstraction          : 0.09
% 8.59/3.37  MUC search           : 0.00
% 8.59/3.37  Cooper               : 0.00
% 8.59/3.37  Total                : 2.62
% 8.59/3.37  Index Insertion      : 0.00
% 8.59/3.37  Index Deletion       : 0.00
% 8.59/3.37  Index Matching       : 0.00
% 8.59/3.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
