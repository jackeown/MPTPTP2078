%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:18 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   48 (  63 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 (  75 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_308,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | k4_xboole_0(A_41,B_42) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_84,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_320,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_308,c_84])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_85,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_85])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_227,plain,(
    r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_14])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_242,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_227,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_272,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_2])).

tff(c_99,plain,(
    ! [A_11,B_12] : k4_xboole_0(k4_xboole_0(A_11,B_12),A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_85])).

tff(c_133,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_156,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_133])).

tff(c_665,plain,(
    ! [A_55,B_56,C_57] : k4_xboole_0(k3_xboole_0(A_55,B_56),C_57) = k3_xboole_0(A_55,k4_xboole_0(B_56,C_57)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_763,plain,(
    ! [C_59] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_59)) = k4_xboole_0('#skF_1',C_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_665])).

tff(c_793,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_763])).

tff(c_799,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_793])).

tff(c_801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_799])).

tff(c_802,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_804,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_823,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_804])).

tff(c_1031,plain,(
    ! [A_68,B_69,C_70] : k4_xboole_0(k3_xboole_0(A_68,B_69),C_70) = k3_xboole_0(A_68,k4_xboole_0(B_69,C_70)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1262,plain,(
    ! [A_79,B_80,C_81] : r1_xboole_0(k3_xboole_0(A_79,k4_xboole_0(B_80,C_81)),C_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_1031,c_18])).

tff(c_1292,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_823,c_1262])).

tff(c_1303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_802,c_1292])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:15:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.47  
% 2.72/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.48  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.72/1.48  
% 2.72/1.48  %Foreground sorts:
% 2.72/1.48  
% 2.72/1.48  
% 2.72/1.48  %Background operators:
% 2.72/1.48  
% 2.72/1.48  
% 2.72/1.48  %Foreground operators:
% 2.72/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.72/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.72/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.72/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.72/1.48  
% 2.72/1.49  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.72/1.49  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.72/1.49  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.72/1.49  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.72/1.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.72/1.49  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.72/1.49  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.72/1.49  tff(c_308, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | k4_xboole_0(A_41, B_42)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.49  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.72/1.49  tff(c_84, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_22])).
% 2.72/1.49  tff(c_320, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_308, c_84])).
% 2.72/1.49  tff(c_24, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.72/1.49  tff(c_85, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.49  tff(c_100, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_85])).
% 2.72/1.49  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.72/1.49  tff(c_227, plain, (r1_tarski(k1_xboole_0, '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_100, c_14])).
% 2.72/1.49  tff(c_12, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.49  tff(c_242, plain, (k3_xboole_0(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_227, c_12])).
% 2.72/1.49  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.72/1.49  tff(c_272, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_242, c_2])).
% 2.72/1.49  tff(c_99, plain, (![A_11, B_12]: (k4_xboole_0(k4_xboole_0(A_11, B_12), A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_85])).
% 2.72/1.49  tff(c_133, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=A_37 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.49  tff(c_156, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_24, c_133])).
% 2.72/1.49  tff(c_665, plain, (![A_55, B_56, C_57]: (k4_xboole_0(k3_xboole_0(A_55, B_56), C_57)=k3_xboole_0(A_55, k4_xboole_0(B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.72/1.49  tff(c_763, plain, (![C_59]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_59))=k4_xboole_0('#skF_1', C_59))), inference(superposition, [status(thm), theory('equality')], [c_156, c_665])).
% 2.72/1.49  tff(c_793, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_99, c_763])).
% 2.72/1.49  tff(c_799, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_272, c_793])).
% 2.72/1.49  tff(c_801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_320, c_799])).
% 2.72/1.49  tff(c_802, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_22])).
% 2.72/1.49  tff(c_804, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.49  tff(c_823, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_24, c_804])).
% 2.72/1.49  tff(c_1031, plain, (![A_68, B_69, C_70]: (k4_xboole_0(k3_xboole_0(A_68, B_69), C_70)=k3_xboole_0(A_68, k4_xboole_0(B_69, C_70)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.72/1.49  tff(c_18, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.72/1.49  tff(c_1262, plain, (![A_79, B_80, C_81]: (r1_xboole_0(k3_xboole_0(A_79, k4_xboole_0(B_80, C_81)), C_81))), inference(superposition, [status(thm), theory('equality')], [c_1031, c_18])).
% 2.72/1.49  tff(c_1292, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_823, c_1262])).
% 2.72/1.49  tff(c_1303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_802, c_1292])).
% 2.72/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.49  
% 2.72/1.49  Inference rules
% 2.72/1.49  ----------------------
% 2.72/1.49  #Ref     : 0
% 2.72/1.49  #Sup     : 365
% 2.72/1.49  #Fact    : 0
% 2.72/1.49  #Define  : 0
% 2.72/1.49  #Split   : 1
% 2.72/1.49  #Chain   : 0
% 2.72/1.49  #Close   : 0
% 2.72/1.49  
% 2.72/1.49  Ordering : KBO
% 2.72/1.49  
% 2.72/1.49  Simplification rules
% 2.72/1.49  ----------------------
% 2.72/1.49  #Subsume      : 0
% 2.72/1.49  #Demod        : 183
% 2.72/1.49  #Tautology    : 254
% 2.72/1.49  #SimpNegUnit  : 2
% 2.72/1.49  #BackRed      : 0
% 2.72/1.49  
% 2.72/1.49  #Partial instantiations: 0
% 2.72/1.49  #Strategies tried      : 1
% 2.72/1.49  
% 2.72/1.49  Timing (in seconds)
% 2.72/1.49  ----------------------
% 2.72/1.49  Preprocessing        : 0.33
% 2.72/1.49  Parsing              : 0.17
% 2.72/1.49  CNF conversion       : 0.02
% 2.72/1.49  Main loop            : 0.36
% 2.72/1.49  Inferencing          : 0.13
% 2.72/1.49  Reduction            : 0.13
% 2.72/1.49  Demodulation         : 0.10
% 2.72/1.49  BG Simplification    : 0.02
% 2.72/1.49  Subsumption          : 0.05
% 2.72/1.49  Abstraction          : 0.02
% 2.72/1.49  MUC search           : 0.00
% 2.72/1.49  Cooper               : 0.00
% 2.72/1.49  Total                : 0.72
% 2.72/1.49  Index Insertion      : 0.00
% 2.72/1.49  Index Deletion       : 0.00
% 2.72/1.49  Index Matching       : 0.00
% 2.72/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
