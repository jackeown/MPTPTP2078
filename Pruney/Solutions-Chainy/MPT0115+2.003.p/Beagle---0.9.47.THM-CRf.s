%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:26 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  64 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :   40 (  67 expanded)
%              Number of equality atoms :   27 (  40 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_151,plain,(
    ! [A_28,B_29,C_30] : k4_xboole_0(k4_xboole_0(A_28,B_29),C_30) = k4_xboole_0(A_28,k2_xboole_0(B_29,C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1564,plain,(
    ! [A_82,B_83,C_84] : k4_xboole_0(A_82,k2_xboole_0(k4_xboole_0(A_82,B_83),C_84)) = k4_xboole_0(k3_xboole_0(A_82,B_83),C_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_151])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_72,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_72])).

tff(c_90,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_105,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_90])).

tff(c_111,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_105])).

tff(c_428,plain,(
    ! [A_40,B_41,C_42] : r1_tarski(k2_xboole_0(k3_xboole_0(A_40,B_41),k3_xboole_0(A_40,C_42)),k2_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_452,plain,(
    ! [C_42] : r1_tarski(k2_xboole_0('#skF_1',k3_xboole_0('#skF_1',C_42)),k2_xboole_0('#skF_2',C_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_428])).

tff(c_549,plain,(
    ! [C_45] : r1_tarski('#skF_1',k2_xboole_0('#skF_2',C_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_452])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_565,plain,(
    ! [C_45] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_45)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_549,c_6])).

tff(c_195,plain,(
    ! [C_30] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_30)) = k4_xboole_0(k1_xboole_0,C_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_151])).

tff(c_714,plain,(
    ! [C_30] : k4_xboole_0(k1_xboole_0,C_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_195])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_324,plain,(
    ! [C_35] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_35)) = k4_xboole_0(k1_xboole_0,C_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_151])).

tff(c_356,plain,(
    ! [A_1] : k4_xboole_0('#skF_1',k2_xboole_0(A_1,'#skF_2')) = k4_xboole_0(k1_xboole_0,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_324])).

tff(c_761,plain,(
    ! [A_1] : k4_xboole_0('#skF_1',k2_xboole_0(A_1,'#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_714,c_356])).

tff(c_1574,plain,(
    ! [B_83] : k4_xboole_0(k3_xboole_0('#skF_1',B_83),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1564,c_761])).

tff(c_81,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | k4_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_89,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_81,c_18])).

tff(c_1685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1574,c_89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:35:55 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.45  
% 3.20/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.46  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.20/1.46  
% 3.20/1.46  %Foreground sorts:
% 3.20/1.46  
% 3.20/1.46  
% 3.20/1.46  %Background operators:
% 3.20/1.46  
% 3.20/1.46  
% 3.20/1.46  %Foreground operators:
% 3.20/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.20/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.20/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.20/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.20/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.20/1.46  
% 3.20/1.47  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.20/1.47  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.20/1.47  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.20/1.47  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.20/1.47  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 3.20/1.47  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.20/1.47  tff(f_35, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 3.20/1.47  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.20/1.47  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.20/1.47  tff(c_151, plain, (![A_28, B_29, C_30]: (k4_xboole_0(k4_xboole_0(A_28, B_29), C_30)=k4_xboole_0(A_28, k2_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.20/1.47  tff(c_1564, plain, (![A_82, B_83, C_84]: (k4_xboole_0(A_82, k2_xboole_0(k4_xboole_0(A_82, B_83), C_84))=k4_xboole_0(k3_xboole_0(A_82, B_83), C_84))), inference(superposition, [status(thm), theory('equality')], [c_16, c_151])).
% 3.20/1.47  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.20/1.47  tff(c_12, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.20/1.47  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.20/1.47  tff(c_72, plain, (![A_21, B_22]: (k4_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.47  tff(c_76, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_72])).
% 3.20/1.47  tff(c_90, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.20/1.47  tff(c_105, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_76, c_90])).
% 3.20/1.47  tff(c_111, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_105])).
% 3.20/1.47  tff(c_428, plain, (![A_40, B_41, C_42]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_40, B_41), k3_xboole_0(A_40, C_42)), k2_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.20/1.47  tff(c_452, plain, (![C_42]: (r1_tarski(k2_xboole_0('#skF_1', k3_xboole_0('#skF_1', C_42)), k2_xboole_0('#skF_2', C_42)))), inference(superposition, [status(thm), theory('equality')], [c_111, c_428])).
% 3.20/1.47  tff(c_549, plain, (![C_45]: (r1_tarski('#skF_1', k2_xboole_0('#skF_2', C_45)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_452])).
% 3.20/1.47  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.47  tff(c_565, plain, (![C_45]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_45))=k1_xboole_0)), inference(resolution, [status(thm)], [c_549, c_6])).
% 3.20/1.47  tff(c_195, plain, (![C_30]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_30))=k4_xboole_0(k1_xboole_0, C_30))), inference(superposition, [status(thm), theory('equality')], [c_76, c_151])).
% 3.20/1.47  tff(c_714, plain, (![C_30]: (k4_xboole_0(k1_xboole_0, C_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_565, c_195])).
% 3.20/1.47  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.20/1.47  tff(c_324, plain, (![C_35]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_35))=k4_xboole_0(k1_xboole_0, C_35))), inference(superposition, [status(thm), theory('equality')], [c_76, c_151])).
% 3.20/1.47  tff(c_356, plain, (![A_1]: (k4_xboole_0('#skF_1', k2_xboole_0(A_1, '#skF_2'))=k4_xboole_0(k1_xboole_0, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_324])).
% 3.20/1.47  tff(c_761, plain, (![A_1]: (k4_xboole_0('#skF_1', k2_xboole_0(A_1, '#skF_2'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_714, c_356])).
% 3.20/1.47  tff(c_1574, plain, (![B_83]: (k4_xboole_0(k3_xboole_0('#skF_1', B_83), '#skF_2')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1564, c_761])).
% 3.20/1.47  tff(c_81, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | k4_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.47  tff(c_18, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.20/1.47  tff(c_89, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_81, c_18])).
% 3.20/1.47  tff(c_1685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1574, c_89])).
% 3.20/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.47  
% 3.20/1.47  Inference rules
% 3.20/1.47  ----------------------
% 3.20/1.47  #Ref     : 0
% 3.20/1.47  #Sup     : 388
% 3.20/1.47  #Fact    : 0
% 3.20/1.47  #Define  : 0
% 3.20/1.47  #Split   : 0
% 3.20/1.47  #Chain   : 0
% 3.20/1.47  #Close   : 0
% 3.20/1.47  
% 3.20/1.47  Ordering : KBO
% 3.20/1.47  
% 3.20/1.47  Simplification rules
% 3.20/1.47  ----------------------
% 3.20/1.47  #Subsume      : 0
% 3.20/1.47  #Demod        : 327
% 3.20/1.47  #Tautology    : 278
% 3.20/1.47  #SimpNegUnit  : 0
% 3.20/1.47  #BackRed      : 5
% 3.20/1.47  
% 3.20/1.47  #Partial instantiations: 0
% 3.20/1.47  #Strategies tried      : 1
% 3.20/1.47  
% 3.20/1.47  Timing (in seconds)
% 3.20/1.47  ----------------------
% 3.20/1.47  Preprocessing        : 0.26
% 3.20/1.47  Parsing              : 0.15
% 3.20/1.47  CNF conversion       : 0.01
% 3.20/1.47  Main loop            : 0.47
% 3.20/1.47  Inferencing          : 0.16
% 3.20/1.47  Reduction            : 0.19
% 3.20/1.47  Demodulation         : 0.15
% 3.20/1.47  BG Simplification    : 0.02
% 3.20/1.47  Subsumption          : 0.06
% 3.20/1.47  Abstraction          : 0.02
% 3.20/1.47  MUC search           : 0.00
% 3.20/1.47  Cooper               : 0.00
% 3.20/1.47  Total                : 0.75
% 3.20/1.47  Index Insertion      : 0.00
% 3.20/1.47  Index Deletion       : 0.00
% 3.20/1.47  Index Matching       : 0.00
% 3.20/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
