%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:49 EST 2020

% Result     : Theorem 9.05s
% Output     : CNFRefutation 9.05s
% Verified   : 
% Statistics : Number of formulae       :   44 (  70 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   42 (  74 expanded)
%              Number of equality atoms :   24 (  42 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k4_xboole_0(A,B),C)
       => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_17,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_12,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_67,plain,(
    ! [A_21,B_22] :
      ( k2_xboole_0(A_21,B_22) = B_22
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k2_xboole_0(A_13,B_14) ),
    inference(resolution,[status(thm)],[c_12,c_67])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_19,plain,(
    ! [B_17,A_18] : k2_xboole_0(B_17,A_18) = k2_xboole_0(A_18,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_18,B_17] : r1_tarski(A_18,k2_xboole_0(B_17,A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_19,c_12])).

tff(c_2612,plain,(
    ! [A_95,B_96] : k2_xboole_0(A_95,k2_xboole_0(B_96,A_95)) = k2_xboole_0(B_96,A_95) ),
    inference(resolution,[status(thm)],[c_34,c_67])).

tff(c_3063,plain,(
    ! [B_101,A_102] : k2_xboole_0(B_101,k2_xboole_0(B_101,A_102)) = k2_xboole_0(A_102,B_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2612])).

tff(c_3213,plain,(
    ! [B_6,A_5] : k2_xboole_0(k4_xboole_0(B_6,A_5),A_5) = k2_xboole_0(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_3063])).

tff(c_8828,plain,(
    ! [B_152,A_153] : k2_xboole_0(k4_xboole_0(B_152,A_153),A_153) = k2_xboole_0(A_153,B_152) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3213])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k4_xboole_0(A_7,B_8),C_9) = k4_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_79,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_16,c_67])).

tff(c_100,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_79])).

tff(c_151,plain,(
    ! [A_25,B_26,C_27] :
      ( r1_tarski(k4_xboole_0(A_25,B_26),C_27)
      | ~ r1_tarski(A_25,k2_xboole_0(B_26,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_411,plain,(
    ! [A_37,B_38,C_39] :
      ( k2_xboole_0(k4_xboole_0(A_37,B_38),C_39) = C_39
      | ~ r1_tarski(A_37,k2_xboole_0(B_38,C_39)) ) ),
    inference(resolution,[status(thm)],[c_151,c_4])).

tff(c_616,plain,(
    ! [A_47,B_48] : k2_xboole_0(k4_xboole_0(A_47,A_47),B_48) = B_48 ),
    inference(resolution,[status(thm)],[c_12,c_411])).

tff(c_678,plain,(
    ! [A_7,B_8,B_48] : k2_xboole_0(k4_xboole_0(A_7,k2_xboole_0(B_8,k4_xboole_0(A_7,B_8))),B_48) = B_48 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_616])).

tff(c_2813,plain,(
    ! [A_98,B_99,B_100] : k2_xboole_0(k4_xboole_0(A_98,k2_xboole_0(B_99,A_98)),B_100) = B_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_678])).

tff(c_3000,plain,(
    ! [B_100] : k2_xboole_0(k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_3'),B_100) = B_100 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_2813])).

tff(c_3060,plain,(
    ! [B_100] : k2_xboole_0(k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')),B_100) = B_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_3000])).

tff(c_8886,plain,(
    k2_xboole_0(k2_xboole_0('#skF_3','#skF_2'),'#skF_1') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8828,c_3060])).

tff(c_16798,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8886,c_34])).

tff(c_16852,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17,c_16798])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:28:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.05/3.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.05/3.35  
% 9.05/3.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.05/3.35  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 9.05/3.35  
% 9.05/3.35  %Foreground sorts:
% 9.05/3.35  
% 9.05/3.35  
% 9.05/3.35  %Background operators:
% 9.05/3.35  
% 9.05/3.35  
% 9.05/3.35  %Foreground operators:
% 9.05/3.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.05/3.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.05/3.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.05/3.35  tff('#skF_2', type, '#skF_2': $i).
% 9.05/3.35  tff('#skF_3', type, '#skF_3': $i).
% 9.05/3.35  tff('#skF_1', type, '#skF_1': $i).
% 9.05/3.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.05/3.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.05/3.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.05/3.35  
% 9.05/3.36  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.05/3.36  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 9.05/3.36  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 9.05/3.36  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.05/3.36  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.05/3.36  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 9.05/3.36  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 9.05/3.36  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.05/3.36  tff(c_14, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.05/3.36  tff(c_17, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 9.05/3.36  tff(c_12, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.05/3.36  tff(c_67, plain, (![A_21, B_22]: (k2_xboole_0(A_21, B_22)=B_22 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.05/3.36  tff(c_78, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k2_xboole_0(A_13, B_14))), inference(resolution, [status(thm)], [c_12, c_67])).
% 9.05/3.36  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.05/3.36  tff(c_19, plain, (![B_17, A_18]: (k2_xboole_0(B_17, A_18)=k2_xboole_0(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.05/3.36  tff(c_34, plain, (![A_18, B_17]: (r1_tarski(A_18, k2_xboole_0(B_17, A_18)))), inference(superposition, [status(thm), theory('equality')], [c_19, c_12])).
% 9.05/3.36  tff(c_2612, plain, (![A_95, B_96]: (k2_xboole_0(A_95, k2_xboole_0(B_96, A_95))=k2_xboole_0(B_96, A_95))), inference(resolution, [status(thm)], [c_34, c_67])).
% 9.05/3.36  tff(c_3063, plain, (![B_101, A_102]: (k2_xboole_0(B_101, k2_xboole_0(B_101, A_102))=k2_xboole_0(A_102, B_101))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2612])).
% 9.05/3.36  tff(c_3213, plain, (![B_6, A_5]: (k2_xboole_0(k4_xboole_0(B_6, A_5), A_5)=k2_xboole_0(A_5, k2_xboole_0(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_3063])).
% 9.05/3.36  tff(c_8828, plain, (![B_152, A_153]: (k2_xboole_0(k4_xboole_0(B_152, A_153), A_153)=k2_xboole_0(A_153, B_152))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3213])).
% 9.05/3.36  tff(c_8, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k4_xboole_0(A_7, B_8), C_9)=k4_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.05/3.36  tff(c_16, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.05/3.36  tff(c_79, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_16, c_67])).
% 9.05/3.36  tff(c_100, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2, c_79])).
% 9.05/3.36  tff(c_151, plain, (![A_25, B_26, C_27]: (r1_tarski(k4_xboole_0(A_25, B_26), C_27) | ~r1_tarski(A_25, k2_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.05/3.36  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.05/3.36  tff(c_411, plain, (![A_37, B_38, C_39]: (k2_xboole_0(k4_xboole_0(A_37, B_38), C_39)=C_39 | ~r1_tarski(A_37, k2_xboole_0(B_38, C_39)))), inference(resolution, [status(thm)], [c_151, c_4])).
% 9.05/3.36  tff(c_616, plain, (![A_47, B_48]: (k2_xboole_0(k4_xboole_0(A_47, A_47), B_48)=B_48)), inference(resolution, [status(thm)], [c_12, c_411])).
% 9.05/3.36  tff(c_678, plain, (![A_7, B_8, B_48]: (k2_xboole_0(k4_xboole_0(A_7, k2_xboole_0(B_8, k4_xboole_0(A_7, B_8))), B_48)=B_48)), inference(superposition, [status(thm), theory('equality')], [c_8, c_616])).
% 9.05/3.36  tff(c_2813, plain, (![A_98, B_99, B_100]: (k2_xboole_0(k4_xboole_0(A_98, k2_xboole_0(B_99, A_98)), B_100)=B_100)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_678])).
% 9.05/3.36  tff(c_3000, plain, (![B_100]: (k2_xboole_0(k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3'), B_100)=B_100)), inference(superposition, [status(thm), theory('equality')], [c_100, c_2813])).
% 9.05/3.36  tff(c_3060, plain, (![B_100]: (k2_xboole_0(k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2')), B_100)=B_100)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_3000])).
% 9.05/3.36  tff(c_8886, plain, (k2_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), '#skF_1')=k2_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8828, c_3060])).
% 9.05/3.36  tff(c_16798, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8886, c_34])).
% 9.05/3.36  tff(c_16852, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17, c_16798])).
% 9.05/3.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.05/3.36  
% 9.05/3.36  Inference rules
% 9.05/3.36  ----------------------
% 9.05/3.36  #Ref     : 0
% 9.05/3.36  #Sup     : 4129
% 9.05/3.36  #Fact    : 0
% 9.05/3.36  #Define  : 0
% 9.05/3.36  #Split   : 0
% 9.05/3.36  #Chain   : 0
% 9.05/3.36  #Close   : 0
% 9.05/3.36  
% 9.05/3.36  Ordering : KBO
% 9.05/3.36  
% 9.05/3.36  Simplification rules
% 9.05/3.36  ----------------------
% 9.05/3.36  #Subsume      : 283
% 9.05/3.36  #Demod        : 4061
% 9.05/3.36  #Tautology    : 2041
% 9.05/3.36  #SimpNegUnit  : 1
% 9.05/3.36  #BackRed      : 2
% 9.05/3.36  
% 9.05/3.36  #Partial instantiations: 0
% 9.05/3.36  #Strategies tried      : 1
% 9.05/3.36  
% 9.05/3.36  Timing (in seconds)
% 9.05/3.36  ----------------------
% 9.05/3.36  Preprocessing        : 0.25
% 9.05/3.36  Parsing              : 0.14
% 9.05/3.36  CNF conversion       : 0.01
% 9.05/3.36  Main loop            : 2.37
% 9.05/3.36  Inferencing          : 0.51
% 9.05/3.36  Reduction            : 1.32
% 9.05/3.36  Demodulation         : 1.17
% 9.05/3.36  BG Simplification    : 0.07
% 9.05/3.36  Subsumption          : 0.36
% 9.05/3.36  Abstraction          : 0.12
% 9.05/3.36  MUC search           : 0.00
% 9.05/3.36  Cooper               : 0.00
% 9.05/3.36  Total                : 2.64
% 9.05/3.36  Index Insertion      : 0.00
% 9.05/3.36  Index Deletion       : 0.00
% 9.05/3.36  Index Matching       : 0.00
% 9.05/3.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
