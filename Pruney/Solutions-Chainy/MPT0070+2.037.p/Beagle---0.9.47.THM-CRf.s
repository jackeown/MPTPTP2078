%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:23 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   33 (  41 expanded)
%              Number of equality atoms :   21 (  22 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_59,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | k3_xboole_0(A_20,B_21) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_67,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_59,c_20])).

tff(c_12,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_41,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_41])).

tff(c_14,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_50,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_50])).

tff(c_94,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_115,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_94])).

tff(c_125,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_115])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] : k3_xboole_0(k3_xboole_0(A_5,B_6),C_7) = k3_xboole_0(A_5,k3_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_630,plain,(
    ! [C_43] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_43)) = k3_xboole_0('#skF_1',C_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_10])).

tff(c_671,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_630])).

tff(c_687,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_671])).

tff(c_689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_687])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % DateTime   : Tue Dec  1 12:05:06 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.37  
% 2.30/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.37  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.30/1.37  
% 2.30/1.37  %Foreground sorts:
% 2.30/1.37  
% 2.30/1.37  
% 2.30/1.37  %Background operators:
% 2.30/1.37  
% 2.30/1.37  
% 2.30/1.37  %Foreground operators:
% 2.30/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.30/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.30/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.30/1.37  
% 2.30/1.38  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.30/1.38  tff(f_50, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.30/1.38  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.30/1.38  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.30/1.38  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.30/1.38  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.30/1.38  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.30/1.38  tff(c_59, plain, (![A_20, B_21]: (r1_xboole_0(A_20, B_21) | k3_xboole_0(A_20, B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.38  tff(c_20, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.30/1.38  tff(c_67, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_59, c_20])).
% 2.30/1.38  tff(c_12, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.30/1.38  tff(c_22, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.30/1.38  tff(c_41, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.38  tff(c_45, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_41])).
% 2.30/1.38  tff(c_14, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.30/1.38  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.30/1.38  tff(c_50, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.30/1.38  tff(c_54, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_50])).
% 2.30/1.38  tff(c_94, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.30/1.38  tff(c_115, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_54, c_94])).
% 2.30/1.38  tff(c_125, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_115])).
% 2.30/1.38  tff(c_10, plain, (![A_5, B_6, C_7]: (k3_xboole_0(k3_xboole_0(A_5, B_6), C_7)=k3_xboole_0(A_5, k3_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.30/1.38  tff(c_630, plain, (![C_43]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_43))=k3_xboole_0('#skF_1', C_43))), inference(superposition, [status(thm), theory('equality')], [c_125, c_10])).
% 2.30/1.38  tff(c_671, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_45, c_630])).
% 2.30/1.38  tff(c_687, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_671])).
% 2.30/1.38  tff(c_689, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_687])).
% 2.30/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.38  
% 2.30/1.38  Inference rules
% 2.30/1.38  ----------------------
% 2.30/1.38  #Ref     : 0
% 2.30/1.38  #Sup     : 158
% 2.30/1.38  #Fact    : 0
% 2.30/1.38  #Define  : 0
% 2.30/1.38  #Split   : 0
% 2.30/1.38  #Chain   : 0
% 2.30/1.38  #Close   : 0
% 2.30/1.38  
% 2.30/1.38  Ordering : KBO
% 2.30/1.38  
% 2.30/1.38  Simplification rules
% 2.30/1.38  ----------------------
% 2.30/1.38  #Subsume      : 0
% 2.30/1.38  #Demod        : 157
% 2.30/1.38  #Tautology    : 123
% 2.30/1.38  #SimpNegUnit  : 1
% 2.30/1.38  #BackRed      : 0
% 2.30/1.38  
% 2.30/1.38  #Partial instantiations: 0
% 2.30/1.38  #Strategies tried      : 1
% 2.30/1.38  
% 2.30/1.38  Timing (in seconds)
% 2.30/1.38  ----------------------
% 2.30/1.38  Preprocessing        : 0.29
% 2.30/1.38  Parsing              : 0.16
% 2.30/1.38  CNF conversion       : 0.02
% 2.30/1.38  Main loop            : 0.29
% 2.30/1.38  Inferencing          : 0.12
% 2.30/1.38  Reduction            : 0.11
% 2.30/1.38  Demodulation         : 0.08
% 2.30/1.38  BG Simplification    : 0.01
% 2.30/1.38  Subsumption          : 0.04
% 2.30/1.38  Abstraction          : 0.02
% 2.30/1.38  MUC search           : 0.00
% 2.30/1.38  Cooper               : 0.00
% 2.30/1.38  Total                : 0.61
% 2.30/1.38  Index Insertion      : 0.00
% 2.30/1.38  Index Deletion       : 0.00
% 2.30/1.38  Index Matching       : 0.00
% 2.30/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
