%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:17 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   49 (  61 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  68 expanded)
%              Number of equality atoms :   22 (  27 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_278,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | k4_xboole_0(A_49,B_50) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_66,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_290,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_278,c_66])).

tff(c_51,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k2_xboole_0(A_32,B_33)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_59,plain,(
    ! [A_32] : r1_tarski(k1_xboole_0,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_16])).

tff(c_100,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = A_39
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_113,plain,(
    ! [A_41] : k3_xboole_0(k1_xboole_0,A_41) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_59,c_100])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_118,plain,(
    ! [A_41] : k3_xboole_0(A_41,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_2])).

tff(c_188,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = k1_xboole_0
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_199,plain,(
    ! [A_14,B_15] : k4_xboole_0(k4_xboole_0(A_14,B_15),A_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_188])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_112,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_100])).

tff(c_502,plain,(
    ! [A_61,B_62,C_63] : k4_xboole_0(k3_xboole_0(A_61,B_62),C_63) = k3_xboole_0(A_61,k4_xboole_0(B_62,C_63)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_632,plain,(
    ! [C_67] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_67)) = k4_xboole_0('#skF_1',C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_502])).

tff(c_666,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_632])).

tff(c_676,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_666])).

tff(c_678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_290,c_676])).

tff(c_679,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_742,plain,(
    ! [A_72,B_73] :
      ( k3_xboole_0(A_72,B_73) = A_72
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_758,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_742])).

tff(c_1089,plain,(
    ! [A_90,B_91,C_92] : k4_xboole_0(k3_xboole_0(A_90,B_91),C_92) = k3_xboole_0(A_90,k4_xboole_0(B_91,C_92)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_24,B_25] : r1_xboole_0(k4_xboole_0(A_24,B_25),B_25) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1749,plain,(
    ! [A_112,B_113,C_114] : r1_xboole_0(k3_xboole_0(A_112,k4_xboole_0(B_113,C_114)),C_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_1089,c_26])).

tff(c_1780,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_758,c_1749])).

tff(c_1815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_679,c_1780])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:31:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.47  
% 3.05/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.47  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.05/1.47  
% 3.05/1.47  %Foreground sorts:
% 3.05/1.47  
% 3.05/1.47  
% 3.05/1.47  %Background operators:
% 3.05/1.47  
% 3.05/1.47  
% 3.05/1.47  %Foreground operators:
% 3.05/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.05/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.05/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.05/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.05/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.05/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.05/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.05/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.05/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.05/1.47  
% 3.05/1.48  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.05/1.48  tff(f_60, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.05/1.48  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.05/1.48  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.05/1.48  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.05/1.48  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.05/1.48  tff(f_49, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.05/1.48  tff(f_53, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.05/1.48  tff(c_278, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | k4_xboole_0(A_49, B_50)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.05/1.48  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.05/1.48  tff(c_66, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_28])).
% 3.05/1.48  tff(c_290, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_278, c_66])).
% 3.05/1.48  tff(c_51, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k2_xboole_0(A_32, B_33))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.05/1.48  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.05/1.48  tff(c_59, plain, (![A_32]: (r1_tarski(k1_xboole_0, A_32))), inference(superposition, [status(thm), theory('equality')], [c_51, c_16])).
% 3.05/1.48  tff(c_100, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=A_39 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.05/1.48  tff(c_113, plain, (![A_41]: (k3_xboole_0(k1_xboole_0, A_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_59, c_100])).
% 3.05/1.48  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.05/1.48  tff(c_118, plain, (![A_41]: (k3_xboole_0(A_41, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_113, c_2])).
% 3.05/1.48  tff(c_188, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=k1_xboole_0 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.05/1.48  tff(c_199, plain, (![A_14, B_15]: (k4_xboole_0(k4_xboole_0(A_14, B_15), A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_188])).
% 3.05/1.48  tff(c_30, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.05/1.48  tff(c_112, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_30, c_100])).
% 3.05/1.48  tff(c_502, plain, (![A_61, B_62, C_63]: (k4_xboole_0(k3_xboole_0(A_61, B_62), C_63)=k3_xboole_0(A_61, k4_xboole_0(B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.05/1.48  tff(c_632, plain, (![C_67]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_67))=k4_xboole_0('#skF_1', C_67))), inference(superposition, [status(thm), theory('equality')], [c_112, c_502])).
% 3.05/1.48  tff(c_666, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_199, c_632])).
% 3.05/1.48  tff(c_676, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_118, c_666])).
% 3.05/1.48  tff(c_678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_290, c_676])).
% 3.05/1.48  tff(c_679, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 3.05/1.48  tff(c_742, plain, (![A_72, B_73]: (k3_xboole_0(A_72, B_73)=A_72 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.05/1.48  tff(c_758, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_30, c_742])).
% 3.05/1.48  tff(c_1089, plain, (![A_90, B_91, C_92]: (k4_xboole_0(k3_xboole_0(A_90, B_91), C_92)=k3_xboole_0(A_90, k4_xboole_0(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.05/1.48  tff(c_26, plain, (![A_24, B_25]: (r1_xboole_0(k4_xboole_0(A_24, B_25), B_25))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.05/1.48  tff(c_1749, plain, (![A_112, B_113, C_114]: (r1_xboole_0(k3_xboole_0(A_112, k4_xboole_0(B_113, C_114)), C_114))), inference(superposition, [status(thm), theory('equality')], [c_1089, c_26])).
% 3.05/1.48  tff(c_1780, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_758, c_1749])).
% 3.05/1.48  tff(c_1815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_679, c_1780])).
% 3.05/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.48  
% 3.05/1.48  Inference rules
% 3.05/1.48  ----------------------
% 3.05/1.48  #Ref     : 0
% 3.05/1.48  #Sup     : 447
% 3.05/1.48  #Fact    : 0
% 3.05/1.48  #Define  : 0
% 3.05/1.48  #Split   : 1
% 3.05/1.48  #Chain   : 0
% 3.05/1.48  #Close   : 0
% 3.05/1.48  
% 3.05/1.48  Ordering : KBO
% 3.05/1.48  
% 3.05/1.48  Simplification rules
% 3.05/1.48  ----------------------
% 3.05/1.48  #Subsume      : 0
% 3.05/1.48  #Demod        : 240
% 3.05/1.48  #Tautology    : 304
% 3.05/1.48  #SimpNegUnit  : 2
% 3.05/1.48  #BackRed      : 0
% 3.05/1.48  
% 3.05/1.48  #Partial instantiations: 0
% 3.05/1.48  #Strategies tried      : 1
% 3.05/1.48  
% 3.05/1.48  Timing (in seconds)
% 3.05/1.48  ----------------------
% 3.05/1.48  Preprocessing        : 0.29
% 3.05/1.48  Parsing              : 0.16
% 3.05/1.48  CNF conversion       : 0.02
% 3.05/1.48  Main loop            : 0.43
% 3.05/1.48  Inferencing          : 0.15
% 3.05/1.48  Reduction            : 0.17
% 3.05/1.48  Demodulation         : 0.14
% 3.05/1.48  BG Simplification    : 0.02
% 3.05/1.48  Subsumption          : 0.06
% 3.05/1.48  Abstraction          : 0.02
% 3.05/1.48  MUC search           : 0.00
% 3.05/1.48  Cooper               : 0.00
% 3.05/1.48  Total                : 0.75
% 3.05/1.48  Index Insertion      : 0.00
% 3.05/1.48  Index Deletion       : 0.00
% 3.05/1.48  Index Matching       : 0.00
% 3.05/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
