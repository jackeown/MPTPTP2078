%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:18 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   40 (  47 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  52 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_16,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_54,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_18,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_55,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_63,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_18,c_55])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14] : k4_xboole_0(k3_xboole_0(A_12,B_13),C_14) = k3_xboole_0(A_12,k4_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,(
    ! [A_25,B_26,C_27] :
      ( r1_tarski(A_25,B_26)
      | ~ r1_tarski(A_25,k3_xboole_0(B_26,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_101,plain,(
    ! [B_30,C_31,B_32] : r1_tarski(k4_xboole_0(k3_xboole_0(B_30,C_31),B_32),B_30) ),
    inference(resolution,[status(thm)],[c_10,c_68])).

tff(c_114,plain,(
    ! [B_2,A_1,B_32] : r1_tarski(k4_xboole_0(k3_xboole_0(B_2,A_1),B_32),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_101])).

tff(c_331,plain,(
    ! [B_54,A_55,B_56] : r1_tarski(k3_xboole_0(B_54,k4_xboole_0(A_55,B_56)),A_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_114])).

tff(c_344,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_331])).

tff(c_357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_344])).

tff(c_358,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_360,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = A_57
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_372,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_18,c_360])).

tff(c_494,plain,(
    ! [A_71,B_72,C_73] : k4_xboole_0(k3_xboole_0(A_71,B_72),C_73) = k3_xboole_0(A_71,k4_xboole_0(B_72,C_73)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_599,plain,(
    ! [A_78,B_79,C_80] : r1_xboole_0(k3_xboole_0(A_78,k4_xboole_0(B_79,C_80)),C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_14])).

tff(c_608,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_599])).

tff(c_618,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_358,c_608])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:38:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.29  
% 2.28/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.29  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.28/1.29  
% 2.28/1.29  %Foreground sorts:
% 2.28/1.29  
% 2.28/1.29  
% 2.28/1.29  %Background operators:
% 2.28/1.29  
% 2.28/1.29  
% 2.28/1.29  %Foreground operators:
% 2.28/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.28/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.28/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.28/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.28/1.29  
% 2.28/1.30  tff(f_50, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.28/1.30  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.28/1.30  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.28/1.30  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.28/1.30  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.28/1.30  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.28/1.30  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.28/1.30  tff(c_16, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.30  tff(c_54, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_16])).
% 2.28/1.30  tff(c_18, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.30  tff(c_55, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=A_23 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.28/1.30  tff(c_63, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_18, c_55])).
% 2.28/1.30  tff(c_12, plain, (![A_12, B_13, C_14]: (k4_xboole_0(k3_xboole_0(A_12, B_13), C_14)=k3_xboole_0(A_12, k4_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.28/1.30  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.28/1.30  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.28/1.30  tff(c_68, plain, (![A_25, B_26, C_27]: (r1_tarski(A_25, B_26) | ~r1_tarski(A_25, k3_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.28/1.30  tff(c_101, plain, (![B_30, C_31, B_32]: (r1_tarski(k4_xboole_0(k3_xboole_0(B_30, C_31), B_32), B_30))), inference(resolution, [status(thm)], [c_10, c_68])).
% 2.28/1.30  tff(c_114, plain, (![B_2, A_1, B_32]: (r1_tarski(k4_xboole_0(k3_xboole_0(B_2, A_1), B_32), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_101])).
% 2.28/1.30  tff(c_331, plain, (![B_54, A_55, B_56]: (r1_tarski(k3_xboole_0(B_54, k4_xboole_0(A_55, B_56)), A_55))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_114])).
% 2.28/1.30  tff(c_344, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_63, c_331])).
% 2.28/1.30  tff(c_357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_344])).
% 2.28/1.30  tff(c_358, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_16])).
% 2.28/1.30  tff(c_360, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=A_57 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.28/1.30  tff(c_372, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_18, c_360])).
% 2.28/1.30  tff(c_494, plain, (![A_71, B_72, C_73]: (k4_xboole_0(k3_xboole_0(A_71, B_72), C_73)=k3_xboole_0(A_71, k4_xboole_0(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.28/1.30  tff(c_14, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.28/1.30  tff(c_599, plain, (![A_78, B_79, C_80]: (r1_xboole_0(k3_xboole_0(A_78, k4_xboole_0(B_79, C_80)), C_80))), inference(superposition, [status(thm), theory('equality')], [c_494, c_14])).
% 2.28/1.30  tff(c_608, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_372, c_599])).
% 2.28/1.30  tff(c_618, plain, $false, inference(negUnitSimplification, [status(thm)], [c_358, c_608])).
% 2.28/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.30  
% 2.28/1.30  Inference rules
% 2.28/1.30  ----------------------
% 2.28/1.30  #Ref     : 0
% 2.28/1.30  #Sup     : 163
% 2.28/1.30  #Fact    : 0
% 2.28/1.30  #Define  : 0
% 2.28/1.30  #Split   : 1
% 2.28/1.30  #Chain   : 0
% 2.28/1.30  #Close   : 0
% 2.28/1.30  
% 2.28/1.30  Ordering : KBO
% 2.28/1.30  
% 2.28/1.30  Simplification rules
% 2.28/1.30  ----------------------
% 2.28/1.30  #Subsume      : 0
% 2.28/1.30  #Demod        : 38
% 2.28/1.30  #Tautology    : 76
% 2.28/1.30  #SimpNegUnit  : 2
% 2.28/1.30  #BackRed      : 9
% 2.28/1.30  
% 2.28/1.30  #Partial instantiations: 0
% 2.28/1.30  #Strategies tried      : 1
% 2.28/1.30  
% 2.28/1.30  Timing (in seconds)
% 2.28/1.30  ----------------------
% 2.28/1.31  Preprocessing        : 0.27
% 2.28/1.31  Parsing              : 0.14
% 2.28/1.31  CNF conversion       : 0.01
% 2.28/1.31  Main loop            : 0.27
% 2.28/1.31  Inferencing          : 0.10
% 2.28/1.31  Reduction            : 0.10
% 2.28/1.31  Demodulation         : 0.08
% 2.28/1.31  BG Simplification    : 0.01
% 2.28/1.31  Subsumption          : 0.04
% 2.28/1.31  Abstraction          : 0.02
% 2.28/1.31  MUC search           : 0.00
% 2.28/1.31  Cooper               : 0.00
% 2.28/1.31  Total                : 0.57
% 2.28/1.31  Index Insertion      : 0.00
% 2.28/1.31  Index Deletion       : 0.00
% 2.28/1.31  Index Matching       : 0.00
% 2.28/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
