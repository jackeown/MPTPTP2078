%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:17 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   43 (  51 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  57 expanded)
%              Number of equality atoms :   18 (  21 expanded)
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

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_327,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | k4_xboole_0(A_44,B_45) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_121,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_339,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_327,c_121])).

tff(c_14,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_168,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_179,plain,(
    ! [A_12,B_13] : k4_xboole_0(k4_xboole_0(A_12,B_13),A_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_168])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_304,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = A_42
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_322,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_304])).

tff(c_522,plain,(
    ! [A_56,B_57,C_58] : k4_xboole_0(k3_xboole_0(A_56,B_57),C_58) = k3_xboole_0(A_56,k4_xboole_0(B_57,C_58)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_728,plain,(
    ! [C_63] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_63)) = k4_xboole_0('#skF_1',C_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_522])).

tff(c_760,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_728])).

tff(c_773,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_760])).

tff(c_775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_339,c_773])).

tff(c_776,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_909,plain,(
    ! [A_70,B_71] :
      ( k3_xboole_0(A_70,B_71) = A_70
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_931,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_909])).

tff(c_1163,plain,(
    ! [A_83,B_84,C_85] : k4_xboole_0(k3_xboole_0(A_83,B_84),C_85) = k3_xboole_0(A_83,k4_xboole_0(B_84,C_85)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1375,plain,(
    ! [A_92,B_93,C_94] : r1_xboole_0(k3_xboole_0(A_92,k4_xboole_0(B_93,C_94)),C_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_1163,c_24])).

tff(c_1390,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_1375])).

tff(c_1424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_776,c_1390])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:09:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.55  
% 2.75/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.55  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.75/1.55  
% 2.75/1.55  %Foreground sorts:
% 2.75/1.55  
% 2.75/1.55  
% 2.75/1.55  %Background operators:
% 2.75/1.55  
% 2.75/1.55  
% 2.75/1.55  %Foreground operators:
% 2.75/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.75/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.75/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.75/1.55  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.55  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.55  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.75/1.55  
% 2.75/1.56  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.75/1.56  tff(f_58, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.75/1.56  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.75/1.56  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.75/1.56  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.75/1.56  tff(f_49, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.75/1.56  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.75/1.56  tff(c_327, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | k4_xboole_0(A_44, B_45)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.75/1.56  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.75/1.56  tff(c_121, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_26])).
% 2.75/1.56  tff(c_339, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_327, c_121])).
% 2.75/1.56  tff(c_14, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.75/1.56  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.75/1.56  tff(c_168, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.75/1.56  tff(c_179, plain, (![A_12, B_13]: (k4_xboole_0(k4_xboole_0(A_12, B_13), A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_168])).
% 2.75/1.56  tff(c_28, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.75/1.56  tff(c_304, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=A_42 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.75/1.56  tff(c_322, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_28, c_304])).
% 2.75/1.56  tff(c_522, plain, (![A_56, B_57, C_58]: (k4_xboole_0(k3_xboole_0(A_56, B_57), C_58)=k3_xboole_0(A_56, k4_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.75/1.56  tff(c_728, plain, (![C_63]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_63))=k4_xboole_0('#skF_1', C_63))), inference(superposition, [status(thm), theory('equality')], [c_322, c_522])).
% 2.75/1.56  tff(c_760, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_179, c_728])).
% 2.75/1.56  tff(c_773, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_760])).
% 2.75/1.56  tff(c_775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_339, c_773])).
% 2.75/1.56  tff(c_776, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 2.75/1.56  tff(c_909, plain, (![A_70, B_71]: (k3_xboole_0(A_70, B_71)=A_70 | ~r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.75/1.56  tff(c_931, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_28, c_909])).
% 2.75/1.56  tff(c_1163, plain, (![A_83, B_84, C_85]: (k4_xboole_0(k3_xboole_0(A_83, B_84), C_85)=k3_xboole_0(A_83, k4_xboole_0(B_84, C_85)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.75/1.56  tff(c_24, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.75/1.56  tff(c_1375, plain, (![A_92, B_93, C_94]: (r1_xboole_0(k3_xboole_0(A_92, k4_xboole_0(B_93, C_94)), C_94))), inference(superposition, [status(thm), theory('equality')], [c_1163, c_24])).
% 2.75/1.56  tff(c_1390, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_931, c_1375])).
% 2.75/1.56  tff(c_1424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_776, c_1390])).
% 2.75/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.56  
% 2.75/1.56  Inference rules
% 2.75/1.56  ----------------------
% 2.75/1.56  #Ref     : 0
% 2.75/1.56  #Sup     : 351
% 2.75/1.56  #Fact    : 0
% 2.75/1.56  #Define  : 0
% 2.75/1.56  #Split   : 1
% 2.75/1.56  #Chain   : 0
% 2.75/1.56  #Close   : 0
% 2.75/1.56  
% 2.75/1.56  Ordering : KBO
% 2.75/1.56  
% 2.75/1.56  Simplification rules
% 2.75/1.56  ----------------------
% 2.75/1.56  #Subsume      : 0
% 2.75/1.56  #Demod        : 178
% 2.75/1.56  #Tautology    : 246
% 2.75/1.56  #SimpNegUnit  : 2
% 2.75/1.56  #BackRed      : 0
% 2.75/1.56  
% 2.75/1.56  #Partial instantiations: 0
% 2.75/1.56  #Strategies tried      : 1
% 2.75/1.56  
% 2.75/1.56  Timing (in seconds)
% 2.75/1.56  ----------------------
% 2.75/1.56  Preprocessing        : 0.29
% 2.75/1.56  Parsing              : 0.15
% 2.75/1.56  CNF conversion       : 0.02
% 2.75/1.56  Main loop            : 0.36
% 2.75/1.56  Inferencing          : 0.13
% 2.75/1.56  Reduction            : 0.14
% 2.75/1.56  Demodulation         : 0.11
% 2.75/1.56  BG Simplification    : 0.01
% 2.75/1.56  Subsumption          : 0.05
% 2.75/1.56  Abstraction          : 0.02
% 2.75/1.56  MUC search           : 0.00
% 2.75/1.56  Cooper               : 0.00
% 2.75/1.56  Total                : 0.67
% 2.75/1.56  Index Insertion      : 0.00
% 2.75/1.56  Index Deletion       : 0.00
% 2.75/1.56  Index Matching       : 0.00
% 2.75/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
