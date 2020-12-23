%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:19 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   49 (  87 expanded)
%              Number of leaves         :   19 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 ( 111 expanded)
%              Number of equality atoms :   24 (  47 expanded)
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

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_39,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | k4_xboole_0(A_25,B_26) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_25,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_47,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_39,c_25])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_26])).

tff(c_48,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_60,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_48])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_176,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_12])).

tff(c_190,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_176])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_59,plain,(
    ! [A_7,B_8] : k4_xboole_0(k4_xboole_0(A_7,B_8),A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_48])).

tff(c_218,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_59])).

tff(c_213,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_12])).

tff(c_401,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_213])).

tff(c_514,plain,(
    ! [A_50,B_51,C_52] : k4_xboole_0(k3_xboole_0(A_50,B_51),C_52) = k3_xboole_0(A_50,k4_xboole_0(B_51,C_52)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_611,plain,(
    ! [C_54] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_54)) = k4_xboole_0('#skF_1',C_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_514])).

tff(c_639,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_611])).

tff(c_645,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_639])).

tff(c_647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_645])).

tff(c_648,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_753,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(A_61,B_62) = A_61
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_777,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_753])).

tff(c_1249,plain,(
    ! [A_89,B_90,C_91] : k4_xboole_0(k3_xboole_0(A_89,B_90),C_91) = k3_xboole_0(A_89,k4_xboole_0(B_90,C_91)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1636,plain,(
    ! [A_101,B_102,C_103] : r1_xboole_0(k3_xboole_0(A_101,k4_xboole_0(B_102,C_103)),C_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_1249,c_18])).

tff(c_1668,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_777,c_1636])).

tff(c_1686,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_648,c_1668])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.47  
% 3.06/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.47  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.06/1.47  
% 3.06/1.47  %Foreground sorts:
% 3.06/1.47  
% 3.06/1.47  
% 3.06/1.47  %Background operators:
% 3.06/1.47  
% 3.06/1.47  
% 3.06/1.47  %Foreground operators:
% 3.06/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.06/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.06/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.06/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.06/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.06/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.06/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.06/1.47  
% 3.12/1.48  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.12/1.48  tff(f_56, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.12/1.48  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.12/1.48  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.12/1.48  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.12/1.48  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.12/1.48  tff(f_49, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.12/1.48  tff(c_39, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | k4_xboole_0(A_25, B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.12/1.48  tff(c_20, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.12/1.48  tff(c_25, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_20])).
% 3.12/1.48  tff(c_47, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_39, c_25])).
% 3.12/1.48  tff(c_22, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.12/1.48  tff(c_26, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=A_23 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.12/1.48  tff(c_34, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_22, c_26])).
% 3.12/1.48  tff(c_48, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.12/1.48  tff(c_60, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_48])).
% 3.12/1.48  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.12/1.48  tff(c_176, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_60, c_12])).
% 3.12/1.48  tff(c_190, plain, (k4_xboole_0('#skF_1', k1_xboole_0)='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_176])).
% 3.12/1.48  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.12/1.48  tff(c_59, plain, (![A_7, B_8]: (k4_xboole_0(k4_xboole_0(A_7, B_8), A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_48])).
% 3.12/1.48  tff(c_218, plain, (k4_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_190, c_59])).
% 3.12/1.48  tff(c_213, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_190, c_12])).
% 3.12/1.48  tff(c_401, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_218, c_213])).
% 3.12/1.48  tff(c_514, plain, (![A_50, B_51, C_52]: (k4_xboole_0(k3_xboole_0(A_50, B_51), C_52)=k3_xboole_0(A_50, k4_xboole_0(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.12/1.48  tff(c_611, plain, (![C_54]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_54))=k4_xboole_0('#skF_1', C_54))), inference(superposition, [status(thm), theory('equality')], [c_34, c_514])).
% 3.12/1.48  tff(c_639, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_59, c_611])).
% 3.12/1.48  tff(c_645, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_401, c_639])).
% 3.12/1.48  tff(c_647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_645])).
% 3.12/1.48  tff(c_648, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_20])).
% 3.12/1.48  tff(c_753, plain, (![A_61, B_62]: (k3_xboole_0(A_61, B_62)=A_61 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.12/1.48  tff(c_777, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_22, c_753])).
% 3.12/1.48  tff(c_1249, plain, (![A_89, B_90, C_91]: (k4_xboole_0(k3_xboole_0(A_89, B_90), C_91)=k3_xboole_0(A_89, k4_xboole_0(B_90, C_91)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.12/1.48  tff(c_18, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.12/1.48  tff(c_1636, plain, (![A_101, B_102, C_103]: (r1_xboole_0(k3_xboole_0(A_101, k4_xboole_0(B_102, C_103)), C_103))), inference(superposition, [status(thm), theory('equality')], [c_1249, c_18])).
% 3.12/1.48  tff(c_1668, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_777, c_1636])).
% 3.12/1.48  tff(c_1686, plain, $false, inference(negUnitSimplification, [status(thm)], [c_648, c_1668])).
% 3.12/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.48  
% 3.12/1.48  Inference rules
% 3.12/1.48  ----------------------
% 3.12/1.48  #Ref     : 0
% 3.12/1.48  #Sup     : 467
% 3.12/1.48  #Fact    : 0
% 3.12/1.48  #Define  : 0
% 3.12/1.48  #Split   : 1
% 3.12/1.48  #Chain   : 0
% 3.12/1.48  #Close   : 0
% 3.12/1.48  
% 3.12/1.48  Ordering : KBO
% 3.12/1.48  
% 3.12/1.48  Simplification rules
% 3.12/1.48  ----------------------
% 3.12/1.48  #Subsume      : 0
% 3.12/1.48  #Demod        : 284
% 3.12/1.48  #Tautology    : 342
% 3.12/1.48  #SimpNegUnit  : 2
% 3.12/1.48  #BackRed      : 0
% 3.12/1.48  
% 3.12/1.48  #Partial instantiations: 0
% 3.12/1.48  #Strategies tried      : 1
% 3.12/1.48  
% 3.12/1.48  Timing (in seconds)
% 3.12/1.48  ----------------------
% 3.12/1.48  Preprocessing        : 0.29
% 3.12/1.48  Parsing              : 0.16
% 3.12/1.48  CNF conversion       : 0.02
% 3.12/1.49  Main loop            : 0.43
% 3.12/1.49  Inferencing          : 0.16
% 3.12/1.49  Reduction            : 0.15
% 3.12/1.49  Demodulation         : 0.11
% 3.12/1.49  BG Simplification    : 0.02
% 3.12/1.49  Subsumption          : 0.06
% 3.12/1.49  Abstraction          : 0.02
% 3.12/1.49  MUC search           : 0.00
% 3.12/1.49  Cooper               : 0.00
% 3.12/1.49  Total                : 0.75
% 3.12/1.49  Index Insertion      : 0.00
% 3.12/1.49  Index Deletion       : 0.00
% 3.12/1.49  Index Matching       : 0.00
% 3.12/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
