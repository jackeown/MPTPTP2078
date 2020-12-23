%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:15 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   47 (  60 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  75 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_59,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | k4_xboole_0(A_25,B_26) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_25,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_63,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_59,c_25])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_81,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_81])).

tff(c_12,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_190,plain,(
    r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_12])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_206,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_190,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_233,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_2])).

tff(c_92,plain,(
    ! [A_9,B_10] : k4_xboole_0(k4_xboole_0(A_9,B_10),A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_81])).

tff(c_64,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_76,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_64])).

tff(c_341,plain,(
    ! [A_47,B_48,C_49] : k4_xboole_0(k3_xboole_0(A_47,B_48),C_49) = k3_xboole_0(A_47,k4_xboole_0(B_48,C_49)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_419,plain,(
    ! [C_51] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_51)) = k4_xboole_0('#skF_1',C_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_341])).

tff(c_435,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_419])).

tff(c_438,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_435])).

tff(c_440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_438])).

tff(c_441,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_18,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_785,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_xboole_0(A_71,C_72)
      | ~ r1_xboole_0(B_73,C_72)
      | ~ r1_tarski(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_861,plain,(
    ! [A_78,B_79,A_80] :
      ( r1_xboole_0(A_78,B_79)
      | ~ r1_tarski(A_78,k4_xboole_0(A_80,B_79)) ) ),
    inference(resolution,[status(thm)],[c_18,c_785])).

tff(c_893,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_861])).

tff(c_901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_441,c_893])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:19:01 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.55  
% 2.73/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.55  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.73/1.55  
% 2.73/1.55  %Foreground sorts:
% 2.73/1.55  
% 2.73/1.55  
% 2.73/1.55  %Background operators:
% 2.73/1.55  
% 2.73/1.55  
% 2.73/1.55  %Foreground operators:
% 2.73/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.73/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.73/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.73/1.55  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.55  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.55  tff('#skF_1', type, '#skF_1': $i).
% 2.73/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.73/1.55  
% 2.73/1.56  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.73/1.56  tff(f_56, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.73/1.56  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.73/1.56  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.73/1.56  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.73/1.56  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.73/1.56  tff(f_49, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.73/1.56  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.73/1.56  tff(c_59, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | k4_xboole_0(A_25, B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.56  tff(c_20, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.73/1.56  tff(c_25, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_20])).
% 2.73/1.56  tff(c_63, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_59, c_25])).
% 2.73/1.56  tff(c_22, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.73/1.56  tff(c_81, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.56  tff(c_93, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_81])).
% 2.73/1.56  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.73/1.56  tff(c_190, plain, (r1_tarski(k1_xboole_0, '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_93, c_12])).
% 2.73/1.56  tff(c_10, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.73/1.56  tff(c_206, plain, (k3_xboole_0(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_190, c_10])).
% 2.73/1.56  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.73/1.56  tff(c_233, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_206, c_2])).
% 2.73/1.56  tff(c_92, plain, (![A_9, B_10]: (k4_xboole_0(k4_xboole_0(A_9, B_10), A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_81])).
% 2.73/1.56  tff(c_64, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.73/1.56  tff(c_76, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_22, c_64])).
% 2.73/1.56  tff(c_341, plain, (![A_47, B_48, C_49]: (k4_xboole_0(k3_xboole_0(A_47, B_48), C_49)=k3_xboole_0(A_47, k4_xboole_0(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.73/1.56  tff(c_419, plain, (![C_51]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_51))=k4_xboole_0('#skF_1', C_51))), inference(superposition, [status(thm), theory('equality')], [c_76, c_341])).
% 2.73/1.56  tff(c_435, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_92, c_419])).
% 2.73/1.56  tff(c_438, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_233, c_435])).
% 2.73/1.56  tff(c_440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_438])).
% 2.73/1.56  tff(c_441, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_20])).
% 2.73/1.56  tff(c_18, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.56  tff(c_785, plain, (![A_71, C_72, B_73]: (r1_xboole_0(A_71, C_72) | ~r1_xboole_0(B_73, C_72) | ~r1_tarski(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.73/1.56  tff(c_861, plain, (![A_78, B_79, A_80]: (r1_xboole_0(A_78, B_79) | ~r1_tarski(A_78, k4_xboole_0(A_80, B_79)))), inference(resolution, [status(thm)], [c_18, c_785])).
% 2.73/1.56  tff(c_893, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_861])).
% 2.73/1.56  tff(c_901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_441, c_893])).
% 2.73/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.56  
% 2.73/1.56  Inference rules
% 2.73/1.56  ----------------------
% 2.73/1.56  #Ref     : 0
% 2.73/1.56  #Sup     : 253
% 2.73/1.56  #Fact    : 0
% 2.73/1.56  #Define  : 0
% 2.73/1.56  #Split   : 1
% 2.73/1.56  #Chain   : 0
% 2.73/1.56  #Close   : 0
% 2.73/1.56  
% 2.73/1.56  Ordering : KBO
% 2.73/1.56  
% 2.73/1.56  Simplification rules
% 2.73/1.56  ----------------------
% 2.73/1.56  #Subsume      : 6
% 2.73/1.56  #Demod        : 104
% 2.73/1.56  #Tautology    : 177
% 2.73/1.56  #SimpNegUnit  : 2
% 2.73/1.56  #BackRed      : 0
% 2.73/1.56  
% 2.73/1.56  #Partial instantiations: 0
% 2.73/1.56  #Strategies tried      : 1
% 2.73/1.56  
% 2.73/1.56  Timing (in seconds)
% 2.73/1.56  ----------------------
% 2.73/1.56  Preprocessing        : 0.36
% 2.73/1.56  Parsing              : 0.21
% 2.73/1.56  CNF conversion       : 0.02
% 2.73/1.56  Main loop            : 0.35
% 2.73/1.56  Inferencing          : 0.13
% 2.73/1.56  Reduction            : 0.12
% 2.73/1.57  Demodulation         : 0.09
% 2.73/1.57  BG Simplification    : 0.02
% 2.73/1.57  Subsumption          : 0.05
% 2.73/1.57  Abstraction          : 0.02
% 2.73/1.57  MUC search           : 0.00
% 2.73/1.57  Cooper               : 0.00
% 2.73/1.57  Total                : 0.73
% 2.73/1.57  Index Insertion      : 0.00
% 2.73/1.57  Index Deletion       : 0.00
% 2.73/1.57  Index Matching       : 0.00
% 2.73/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
