%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:23 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   51 (  85 expanded)
%              Number of leaves         :   19 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   47 (  94 expanded)
%              Number of equality atoms :   33 (  61 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_172,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(A_26,B_27)
      | k3_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_176,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_172,c_20])).

tff(c_12,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_38,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_46,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_38])).

tff(c_195,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_233,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_195])).

tff(c_242,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_233])).

tff(c_22,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_177,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_185,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_177])).

tff(c_300,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k3_xboole_0(A_37,B_38)) = k4_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_334,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_300])).

tff(c_349,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_334])).

tff(c_393,plain,(
    ! [A_41,B_42,C_43] : k4_xboole_0(k3_xboole_0(A_41,B_42),C_43) = k3_xboole_0(A_41,k4_xboole_0(B_42,C_43)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1521,plain,(
    ! [C_65] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_65)) = k4_xboole_0('#skF_1',C_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_393])).

tff(c_1569,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_1521])).

tff(c_1598,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_1569])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_45,plain,(
    ! [A_5,B_6] : k4_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_38])).

tff(c_467,plain,(
    ! [A_44,B_45] : k4_xboole_0(k3_xboole_0(A_44,B_45),A_44) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_45])).

tff(c_18,plain,(
    ! [A_12,B_13,C_14] : k4_xboole_0(k3_xboole_0(A_12,B_13),C_14) = k3_xboole_0(A_12,k4_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_524,plain,(
    ! [A_46,B_47] : k3_xboole_0(A_46,k4_xboole_0(B_47,A_46)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_18])).

tff(c_14,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_538,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k4_xboole_0(B_47,A_46)) = k4_xboole_0(A_46,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_14])).

tff(c_703,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k4_xboole_0(B_51,A_50)) = A_50 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_538])).

tff(c_472,plain,(
    ! [A_44,B_45] : k3_xboole_0(A_44,k4_xboole_0(B_45,A_44)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_18])).

tff(c_712,plain,(
    ! [B_51,A_50] : k3_xboole_0(k4_xboole_0(B_51,A_50),A_50) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_703,c_472])).

tff(c_1608,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1598,c_712])).

tff(c_1628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_1608])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:55:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.48  
% 2.88/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.49  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.88/1.49  
% 2.88/1.49  %Foreground sorts:
% 2.88/1.49  
% 2.88/1.49  
% 2.88/1.49  %Background operators:
% 2.88/1.49  
% 2.88/1.49  
% 2.88/1.49  %Foreground operators:
% 2.88/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.88/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.88/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.88/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.88/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.88/1.49  
% 2.88/1.50  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.88/1.50  tff(f_50, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.88/1.50  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.88/1.50  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.88/1.50  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.88/1.50  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.88/1.50  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.88/1.50  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.88/1.50  tff(c_172, plain, (![A_26, B_27]: (r1_xboole_0(A_26, B_27) | k3_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.88/1.50  tff(c_20, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.88/1.50  tff(c_176, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_172, c_20])).
% 2.88/1.50  tff(c_12, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.88/1.50  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.88/1.50  tff(c_38, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.88/1.50  tff(c_46, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_38])).
% 2.88/1.50  tff(c_195, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.88/1.50  tff(c_233, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_46, c_195])).
% 2.88/1.50  tff(c_242, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_233])).
% 2.88/1.50  tff(c_22, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.88/1.50  tff(c_177, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.88/1.50  tff(c_185, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_177])).
% 2.88/1.50  tff(c_300, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k3_xboole_0(A_37, B_38))=k4_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.88/1.50  tff(c_334, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_185, c_300])).
% 2.88/1.50  tff(c_349, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_334])).
% 2.88/1.50  tff(c_393, plain, (![A_41, B_42, C_43]: (k4_xboole_0(k3_xboole_0(A_41, B_42), C_43)=k3_xboole_0(A_41, k4_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.88/1.50  tff(c_1521, plain, (![C_65]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_65))=k4_xboole_0('#skF_1', C_65))), inference(superposition, [status(thm), theory('equality')], [c_242, c_393])).
% 2.88/1.50  tff(c_1569, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_349, c_1521])).
% 2.88/1.50  tff(c_1598, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_242, c_1569])).
% 2.88/1.50  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.88/1.50  tff(c_45, plain, (![A_5, B_6]: (k4_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_38])).
% 2.88/1.50  tff(c_467, plain, (![A_44, B_45]: (k4_xboole_0(k3_xboole_0(A_44, B_45), A_44)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_195, c_45])).
% 2.88/1.50  tff(c_18, plain, (![A_12, B_13, C_14]: (k4_xboole_0(k3_xboole_0(A_12, B_13), C_14)=k3_xboole_0(A_12, k4_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.88/1.50  tff(c_524, plain, (![A_46, B_47]: (k3_xboole_0(A_46, k4_xboole_0(B_47, A_46))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_467, c_18])).
% 2.88/1.50  tff(c_14, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.88/1.50  tff(c_538, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k4_xboole_0(B_47, A_46))=k4_xboole_0(A_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_524, c_14])).
% 2.88/1.50  tff(c_703, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k4_xboole_0(B_51, A_50))=A_50)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_538])).
% 2.88/1.50  tff(c_472, plain, (![A_44, B_45]: (k3_xboole_0(A_44, k4_xboole_0(B_45, A_44))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_467, c_18])).
% 2.88/1.50  tff(c_712, plain, (![B_51, A_50]: (k3_xboole_0(k4_xboole_0(B_51, A_50), A_50)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_703, c_472])).
% 2.88/1.50  tff(c_1608, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1598, c_712])).
% 2.88/1.50  tff(c_1628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_1608])).
% 2.88/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.50  
% 2.88/1.50  Inference rules
% 2.88/1.50  ----------------------
% 2.88/1.50  #Ref     : 0
% 2.88/1.50  #Sup     : 409
% 2.88/1.50  #Fact    : 0
% 2.88/1.50  #Define  : 0
% 2.88/1.50  #Split   : 0
% 2.88/1.50  #Chain   : 0
% 2.88/1.50  #Close   : 0
% 2.88/1.50  
% 2.88/1.50  Ordering : KBO
% 2.88/1.50  
% 2.88/1.50  Simplification rules
% 2.88/1.50  ----------------------
% 2.88/1.50  #Subsume      : 0
% 2.88/1.50  #Demod        : 305
% 2.88/1.50  #Tautology    : 311
% 2.88/1.50  #SimpNegUnit  : 1
% 2.88/1.50  #BackRed      : 0
% 2.88/1.50  
% 2.88/1.50  #Partial instantiations: 0
% 2.88/1.50  #Strategies tried      : 1
% 2.88/1.50  
% 2.88/1.50  Timing (in seconds)
% 2.88/1.50  ----------------------
% 2.88/1.50  Preprocessing        : 0.28
% 2.88/1.50  Parsing              : 0.16
% 2.88/1.50  CNF conversion       : 0.02
% 2.88/1.50  Main loop            : 0.39
% 2.88/1.50  Inferencing          : 0.15
% 2.88/1.50  Reduction            : 0.15
% 2.88/1.50  Demodulation         : 0.12
% 2.88/1.50  BG Simplification    : 0.01
% 2.88/1.50  Subsumption          : 0.05
% 2.88/1.50  Abstraction          : 0.02
% 2.88/1.50  MUC search           : 0.00
% 2.88/1.50  Cooper               : 0.00
% 2.88/1.50  Total                : 0.70
% 2.88/1.50  Index Insertion      : 0.00
% 2.88/1.50  Index Deletion       : 0.00
% 2.88/1.50  Index Matching       : 0.00
% 2.88/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
