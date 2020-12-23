%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:15 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   47 (  64 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  74 expanded)
%              Number of equality atoms :   16 (  23 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_28,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_137,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_622,plain,(
    ! [A_65,C_66,B_67] :
      ( r1_tarski(A_65,C_66)
      | ~ r1_tarski(B_67,C_66)
      | ~ r1_tarski(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_686,plain,(
    ! [A_72,A_73,B_74] :
      ( r1_tarski(A_72,A_73)
      | ~ r1_tarski(A_72,k4_xboole_0(A_73,B_74)) ) ),
    inference(resolution,[status(thm)],[c_14,c_622])).

tff(c_711,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_686])).

tff(c_729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_711])).

tff(c_730,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_749,plain,(
    ! [A_78,B_79] :
      ( k2_xboole_0(A_78,B_79) = B_79
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_769,plain,(
    ! [A_13,B_14] : k2_xboole_0(k4_xboole_0(A_13,B_14),A_13) = A_13 ),
    inference(resolution,[status(thm)],[c_14,c_749])).

tff(c_18,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_47,plain,(
    ! [A_29,B_30] : r1_tarski(k4_xboole_0(A_29,B_30),A_29) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_50,plain,(
    ! [A_17] : r1_tarski(A_17,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_47])).

tff(c_822,plain,(
    ! [A_82,B_83] :
      ( k3_xboole_0(A_82,B_83) = A_82
      | ~ r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_842,plain,(
    ! [A_17] : k3_xboole_0(A_17,A_17) = A_17 ),
    inference(resolution,[status(thm)],[c_50,c_822])).

tff(c_1832,plain,(
    ! [A_124,B_125,C_126] : k2_xboole_0(k4_xboole_0(A_124,B_125),k3_xboole_0(A_124,C_126)) = k4_xboole_0(A_124,k4_xboole_0(B_125,C_126)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1868,plain,(
    ! [A_17,B_125] : k4_xboole_0(A_17,k4_xboole_0(B_125,A_17)) = k2_xboole_0(k4_xboole_0(A_17,B_125),A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_842,c_1832])).

tff(c_1902,plain,(
    ! [A_17,B_125] : k4_xboole_0(A_17,k4_xboole_0(B_125,A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_1868])).

tff(c_841,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_822])).

tff(c_1862,plain,(
    ! [B_125] : k4_xboole_0('#skF_1',k4_xboole_0(B_125,k4_xboole_0('#skF_2','#skF_3'))) = k2_xboole_0(k4_xboole_0('#skF_1',B_125),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_841,c_1832])).

tff(c_2496,plain,(
    ! [B_141] : k4_xboole_0('#skF_1',k4_xboole_0(B_141,k4_xboole_0('#skF_2','#skF_3'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_1862])).

tff(c_2546,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1902,c_2496])).

tff(c_24,plain,(
    ! [A_23,B_24] : r1_xboole_0(k4_xboole_0(A_23,B_24),B_24) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2614,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2546,c_24])).

tff(c_2631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_730,c_2614])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:48:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.60  
% 3.26/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.60  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.26/1.60  
% 3.26/1.60  %Foreground sorts:
% 3.26/1.60  
% 3.26/1.60  
% 3.26/1.60  %Background operators:
% 3.26/1.60  
% 3.26/1.60  
% 3.26/1.60  %Foreground operators:
% 3.26/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.26/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.26/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.26/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.26/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.26/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.26/1.60  
% 3.26/1.61  tff(f_66, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.26/1.61  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.26/1.61  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.26/1.61  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.26/1.61  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.26/1.61  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.26/1.61  tff(f_55, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.26/1.61  tff(f_57, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.26/1.61  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.26/1.61  tff(c_137, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_28])).
% 3.26/1.61  tff(c_30, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.26/1.61  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.26/1.61  tff(c_622, plain, (![A_65, C_66, B_67]: (r1_tarski(A_65, C_66) | ~r1_tarski(B_67, C_66) | ~r1_tarski(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.26/1.61  tff(c_686, plain, (![A_72, A_73, B_74]: (r1_tarski(A_72, A_73) | ~r1_tarski(A_72, k4_xboole_0(A_73, B_74)))), inference(resolution, [status(thm)], [c_14, c_622])).
% 3.26/1.61  tff(c_711, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_686])).
% 3.26/1.61  tff(c_729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_711])).
% 3.26/1.61  tff(c_730, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 3.26/1.61  tff(c_749, plain, (![A_78, B_79]: (k2_xboole_0(A_78, B_79)=B_79 | ~r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.26/1.61  tff(c_769, plain, (![A_13, B_14]: (k2_xboole_0(k4_xboole_0(A_13, B_14), A_13)=A_13)), inference(resolution, [status(thm)], [c_14, c_749])).
% 3.26/1.61  tff(c_18, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.26/1.61  tff(c_47, plain, (![A_29, B_30]: (r1_tarski(k4_xboole_0(A_29, B_30), A_29))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.26/1.61  tff(c_50, plain, (![A_17]: (r1_tarski(A_17, A_17))), inference(superposition, [status(thm), theory('equality')], [c_18, c_47])).
% 3.26/1.61  tff(c_822, plain, (![A_82, B_83]: (k3_xboole_0(A_82, B_83)=A_82 | ~r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.26/1.61  tff(c_842, plain, (![A_17]: (k3_xboole_0(A_17, A_17)=A_17)), inference(resolution, [status(thm)], [c_50, c_822])).
% 3.26/1.61  tff(c_1832, plain, (![A_124, B_125, C_126]: (k2_xboole_0(k4_xboole_0(A_124, B_125), k3_xboole_0(A_124, C_126))=k4_xboole_0(A_124, k4_xboole_0(B_125, C_126)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.26/1.61  tff(c_1868, plain, (![A_17, B_125]: (k4_xboole_0(A_17, k4_xboole_0(B_125, A_17))=k2_xboole_0(k4_xboole_0(A_17, B_125), A_17))), inference(superposition, [status(thm), theory('equality')], [c_842, c_1832])).
% 3.26/1.61  tff(c_1902, plain, (![A_17, B_125]: (k4_xboole_0(A_17, k4_xboole_0(B_125, A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_769, c_1868])).
% 3.26/1.61  tff(c_841, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_30, c_822])).
% 3.26/1.61  tff(c_1862, plain, (![B_125]: (k4_xboole_0('#skF_1', k4_xboole_0(B_125, k4_xboole_0('#skF_2', '#skF_3')))=k2_xboole_0(k4_xboole_0('#skF_1', B_125), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_841, c_1832])).
% 3.26/1.61  tff(c_2496, plain, (![B_141]: (k4_xboole_0('#skF_1', k4_xboole_0(B_141, k4_xboole_0('#skF_2', '#skF_3')))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_769, c_1862])).
% 3.26/1.61  tff(c_2546, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1902, c_2496])).
% 3.26/1.61  tff(c_24, plain, (![A_23, B_24]: (r1_xboole_0(k4_xboole_0(A_23, B_24), B_24))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.26/1.61  tff(c_2614, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2546, c_24])).
% 3.26/1.61  tff(c_2631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_730, c_2614])).
% 3.26/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.61  
% 3.26/1.61  Inference rules
% 3.26/1.61  ----------------------
% 3.26/1.61  #Ref     : 0
% 3.26/1.61  #Sup     : 649
% 3.26/1.61  #Fact    : 0
% 3.26/1.61  #Define  : 0
% 3.26/1.61  #Split   : 1
% 3.26/1.61  #Chain   : 0
% 3.26/1.61  #Close   : 0
% 3.26/1.61  
% 3.26/1.61  Ordering : KBO
% 3.26/1.61  
% 3.26/1.61  Simplification rules
% 3.26/1.61  ----------------------
% 3.26/1.61  #Subsume      : 13
% 3.26/1.61  #Demod        : 395
% 3.26/1.61  #Tautology    : 488
% 3.26/1.61  #SimpNegUnit  : 2
% 3.26/1.61  #BackRed      : 1
% 3.26/1.61  
% 3.26/1.61  #Partial instantiations: 0
% 3.26/1.61  #Strategies tried      : 1
% 3.26/1.61  
% 3.26/1.61  Timing (in seconds)
% 3.26/1.61  ----------------------
% 3.26/1.62  Preprocessing        : 0.28
% 3.26/1.62  Parsing              : 0.16
% 3.26/1.62  CNF conversion       : 0.02
% 3.26/1.62  Main loop            : 0.52
% 3.26/1.62  Inferencing          : 0.19
% 3.26/1.62  Reduction            : 0.19
% 3.26/1.62  Demodulation         : 0.15
% 3.26/1.62  BG Simplification    : 0.02
% 3.26/1.62  Subsumption          : 0.08
% 3.26/1.62  Abstraction          : 0.03
% 3.26/1.62  MUC search           : 0.00
% 3.26/1.62  Cooper               : 0.00
% 3.26/1.62  Total                : 0.83
% 3.26/1.62  Index Insertion      : 0.00
% 3.26/1.62  Index Deletion       : 0.00
% 3.26/1.62  Index Matching       : 0.00
% 3.26/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
