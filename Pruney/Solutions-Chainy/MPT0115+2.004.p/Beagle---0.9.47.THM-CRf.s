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
% DateTime   : Thu Dec  3 09:45:26 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   41 (  45 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   38 (  45 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_48,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

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
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_105,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_90])).

tff(c_111,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_105])).

tff(c_282,plain,(
    ! [A_40,B_41,C_42] : r1_tarski(k2_xboole_0(k3_xboole_0(A_40,B_41),k3_xboole_0(A_40,C_42)),k2_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_317,plain,(
    ! [B_41] : r1_tarski(k2_xboole_0(k3_xboole_0('#skF_1',B_41),'#skF_1'),k2_xboole_0(B_41,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_282])).

tff(c_341,plain,(
    ! [B_41] : r1_tarski('#skF_1',k2_xboole_0(B_41,'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2,c_317])).

tff(c_151,plain,(
    ! [A_28,B_29,C_30] :
      ( r1_tarski(k4_xboole_0(A_28,B_29),C_30)
      | ~ r1_tarski(A_28,k2_xboole_0(B_29,C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_890,plain,(
    ! [A_65,B_66,C_67] :
      ( k4_xboole_0(k4_xboole_0(A_65,B_66),C_67) = k1_xboole_0
      | ~ r1_tarski(A_65,k2_xboole_0(B_66,C_67)) ) ),
    inference(resolution,[status(thm)],[c_151,c_6])).

tff(c_971,plain,(
    ! [B_69] : k4_xboole_0(k4_xboole_0('#skF_1',B_69),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_341,c_890])).

tff(c_997,plain,(
    ! [B_15] : k4_xboole_0(k3_xboole_0('#skF_1',B_15),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_971])).

tff(c_81,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | k4_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_89,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_81,c_18])).

tff(c_1028,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:51:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.42  
% 2.78/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.42  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.78/1.42  
% 2.78/1.42  %Foreground sorts:
% 2.78/1.42  
% 2.78/1.42  
% 2.78/1.42  %Background operators:
% 2.78/1.42  
% 2.78/1.42  
% 2.78/1.42  %Foreground operators:
% 2.78/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.42  
% 2.78/1.43  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.78/1.43  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.78/1.43  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.78/1.43  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.78/1.43  tff(f_48, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.78/1.43  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.78/1.43  tff(f_35, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.78/1.43  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.78/1.43  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.78/1.43  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.78/1.43  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.78/1.43  tff(c_12, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.78/1.43  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.78/1.43  tff(c_72, plain, (![A_21, B_22]: (k4_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.78/1.43  tff(c_76, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_72])).
% 2.78/1.43  tff(c_90, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.78/1.43  tff(c_105, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_76, c_90])).
% 2.78/1.43  tff(c_111, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_105])).
% 2.78/1.43  tff(c_282, plain, (![A_40, B_41, C_42]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_40, B_41), k3_xboole_0(A_40, C_42)), k2_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.78/1.43  tff(c_317, plain, (![B_41]: (r1_tarski(k2_xboole_0(k3_xboole_0('#skF_1', B_41), '#skF_1'), k2_xboole_0(B_41, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_111, c_282])).
% 2.78/1.43  tff(c_341, plain, (![B_41]: (r1_tarski('#skF_1', k2_xboole_0(B_41, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2, c_317])).
% 2.78/1.43  tff(c_151, plain, (![A_28, B_29, C_30]: (r1_tarski(k4_xboole_0(A_28, B_29), C_30) | ~r1_tarski(A_28, k2_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.78/1.43  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.78/1.43  tff(c_890, plain, (![A_65, B_66, C_67]: (k4_xboole_0(k4_xboole_0(A_65, B_66), C_67)=k1_xboole_0 | ~r1_tarski(A_65, k2_xboole_0(B_66, C_67)))), inference(resolution, [status(thm)], [c_151, c_6])).
% 2.78/1.43  tff(c_971, plain, (![B_69]: (k4_xboole_0(k4_xboole_0('#skF_1', B_69), '#skF_2')=k1_xboole_0)), inference(resolution, [status(thm)], [c_341, c_890])).
% 2.78/1.43  tff(c_997, plain, (![B_15]: (k4_xboole_0(k3_xboole_0('#skF_1', B_15), '#skF_2')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_971])).
% 2.78/1.43  tff(c_81, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | k4_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.78/1.43  tff(c_18, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.78/1.43  tff(c_89, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_81, c_18])).
% 2.78/1.43  tff(c_1028, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_997, c_89])).
% 2.78/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.43  
% 2.78/1.43  Inference rules
% 2.78/1.43  ----------------------
% 2.78/1.43  #Ref     : 0
% 2.78/1.43  #Sup     : 237
% 2.78/1.43  #Fact    : 0
% 2.78/1.43  #Define  : 0
% 2.78/1.43  #Split   : 0
% 2.78/1.43  #Chain   : 0
% 2.78/1.43  #Close   : 0
% 2.78/1.43  
% 2.78/1.43  Ordering : KBO
% 2.78/1.43  
% 2.78/1.43  Simplification rules
% 2.78/1.43  ----------------------
% 2.78/1.43  #Subsume      : 5
% 2.78/1.43  #Demod        : 151
% 2.78/1.43  #Tautology    : 152
% 2.78/1.43  #SimpNegUnit  : 0
% 2.78/1.43  #BackRed      : 1
% 2.78/1.43  
% 2.78/1.43  #Partial instantiations: 0
% 2.78/1.43  #Strategies tried      : 1
% 2.78/1.43  
% 2.78/1.43  Timing (in seconds)
% 2.78/1.43  ----------------------
% 2.78/1.44  Preprocessing        : 0.27
% 2.78/1.44  Parsing              : 0.15
% 2.78/1.44  CNF conversion       : 0.02
% 2.78/1.44  Main loop            : 0.36
% 2.78/1.44  Inferencing          : 0.13
% 2.78/1.44  Reduction            : 0.13
% 2.78/1.44  Demodulation         : 0.11
% 2.78/1.44  BG Simplification    : 0.01
% 2.78/1.44  Subsumption          : 0.06
% 2.78/1.44  Abstraction          : 0.02
% 2.78/1.44  MUC search           : 0.00
% 2.78/1.44  Cooper               : 0.00
% 2.78/1.44  Total                : 0.65
% 2.78/1.44  Index Insertion      : 0.00
% 2.78/1.44  Index Deletion       : 0.00
% 2.78/1.44  Index Matching       : 0.00
% 2.78/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
