%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:47 EST 2020

% Result     : Theorem 5.03s
% Output     : CNFRefutation 5.03s
% Verified   : 
% Statistics : Number of formulae       :   43 (  53 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   41 (  57 expanded)
%              Number of equality atoms :   18 (  23 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(k4_xboole_0(A,B),C)
          & r1_tarski(k4_xboole_0(B,A),C) )
       => r1_tarski(k5_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

tff(c_20,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_37,plain,(
    ! [A_13] : r1_tarski(A_13,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_34])).

tff(c_44,plain,(
    ! [A_23,B_24] :
      ( k2_xboole_0(A_23,B_24) = B_24
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    ! [A_13] : k2_xboole_0(A_13,A_13) = A_13 ),
    inference(resolution,[status(thm)],[c_37,c_44])).

tff(c_95,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37,c_95])).

tff(c_139,plain,(
    ! [A_31,B_32] : k2_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_148,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = k2_xboole_0(A_13,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_139])).

tff(c_154,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_148])).

tff(c_22,plain,(
    r1_tarski(k4_xboole_0('#skF_2','#skF_1'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_114,plain,(
    k4_xboole_0(k4_xboole_0('#skF_2','#skF_1'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_95])).

tff(c_14,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_388,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_1')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_14])).

tff(c_398,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_388])).

tff(c_970,plain,(
    ! [A_59,B_60] : k2_xboole_0(k4_xboole_0(A_59,B_60),k4_xboole_0(B_60,A_59)) = k5_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_tarski(k2_xboole_0(A_14,C_16),k2_xboole_0(B_15,C_16))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4115,plain,(
    ! [A_118,B_119,B_120] :
      ( r1_tarski(k5_xboole_0(A_118,B_119),k2_xboole_0(B_120,k4_xboole_0(B_119,A_118)))
      | ~ r1_tarski(k4_xboole_0(A_118,B_119),B_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_970,c_18])).

tff(c_4179,plain,
    ( r1_tarski(k5_xboole_0('#skF_1','#skF_2'),'#skF_3')
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_4115])).

tff(c_4235,plain,(
    r1_tarski(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4179])).

tff(c_4237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_4235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.03/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.03/1.97  
% 5.03/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.03/1.97  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.03/1.97  
% 5.03/1.97  %Foreground sorts:
% 5.03/1.97  
% 5.03/1.97  
% 5.03/1.97  %Background operators:
% 5.03/1.97  
% 5.03/1.97  
% 5.03/1.97  %Foreground operators:
% 5.03/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.03/1.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.03/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.03/1.97  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.03/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.03/1.97  tff('#skF_2', type, '#skF_2': $i).
% 5.03/1.97  tff('#skF_3', type, '#skF_3': $i).
% 5.03/1.97  tff('#skF_1', type, '#skF_1': $i).
% 5.03/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.03/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.03/1.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.03/1.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.03/1.97  
% 5.03/1.98  tff(f_54, negated_conjecture, ~(![A, B, C]: ((r1_tarski(k4_xboole_0(A, B), C) & r1_tarski(k4_xboole_0(B, A), C)) => r1_tarski(k5_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_xboole_1)).
% 5.03/1.98  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.03/1.98  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.03/1.98  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.03/1.98  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.03/1.98  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.03/1.98  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 5.03/1.98  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_xboole_1)).
% 5.03/1.98  tff(c_20, plain, (~r1_tarski(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.03/1.98  tff(c_24, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.03/1.98  tff(c_16, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.03/1.98  tff(c_34, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.03/1.98  tff(c_37, plain, (![A_13]: (r1_tarski(A_13, A_13))), inference(superposition, [status(thm), theory('equality')], [c_16, c_34])).
% 5.03/1.98  tff(c_44, plain, (![A_23, B_24]: (k2_xboole_0(A_23, B_24)=B_24 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.03/1.98  tff(c_60, plain, (![A_13]: (k2_xboole_0(A_13, A_13)=A_13)), inference(resolution, [status(thm)], [c_37, c_44])).
% 5.03/1.98  tff(c_95, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.03/1.98  tff(c_111, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_37, c_95])).
% 5.03/1.98  tff(c_139, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.03/1.98  tff(c_148, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=k2_xboole_0(A_13, A_13))), inference(superposition, [status(thm), theory('equality')], [c_111, c_139])).
% 5.03/1.98  tff(c_154, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_148])).
% 5.03/1.98  tff(c_22, plain, (r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.03/1.98  tff(c_114, plain, (k4_xboole_0(k4_xboole_0('#skF_2', '#skF_1'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_95])).
% 5.03/1.98  tff(c_14, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.03/1.98  tff(c_388, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_1'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_114, c_14])).
% 5.03/1.98  tff(c_398, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_388])).
% 5.03/1.98  tff(c_970, plain, (![A_59, B_60]: (k2_xboole_0(k4_xboole_0(A_59, B_60), k4_xboole_0(B_60, A_59))=k5_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.03/1.98  tff(c_18, plain, (![A_14, C_16, B_15]: (r1_tarski(k2_xboole_0(A_14, C_16), k2_xboole_0(B_15, C_16)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.03/1.98  tff(c_4115, plain, (![A_118, B_119, B_120]: (r1_tarski(k5_xboole_0(A_118, B_119), k2_xboole_0(B_120, k4_xboole_0(B_119, A_118))) | ~r1_tarski(k4_xboole_0(A_118, B_119), B_120))), inference(superposition, [status(thm), theory('equality')], [c_970, c_18])).
% 5.03/1.98  tff(c_4179, plain, (r1_tarski(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3') | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_398, c_4115])).
% 5.03/1.98  tff(c_4235, plain, (r1_tarski(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4179])).
% 5.03/1.98  tff(c_4237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_4235])).
% 5.03/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.03/1.98  
% 5.03/1.98  Inference rules
% 5.03/1.98  ----------------------
% 5.03/1.98  #Ref     : 0
% 5.03/1.98  #Sup     : 1085
% 5.03/1.98  #Fact    : 0
% 5.03/1.98  #Define  : 0
% 5.03/1.98  #Split   : 5
% 5.03/1.98  #Chain   : 0
% 5.03/1.98  #Close   : 0
% 5.03/1.98  
% 5.03/1.98  Ordering : KBO
% 5.03/1.98  
% 5.03/1.98  Simplification rules
% 5.03/1.98  ----------------------
% 5.03/1.98  #Subsume      : 28
% 5.03/1.98  #Demod        : 799
% 5.03/1.98  #Tautology    : 604
% 5.03/1.98  #SimpNegUnit  : 1
% 5.03/1.98  #BackRed      : 7
% 5.03/1.98  
% 5.03/1.98  #Partial instantiations: 0
% 5.03/1.98  #Strategies tried      : 1
% 5.03/1.98  
% 5.03/1.98  Timing (in seconds)
% 5.03/1.98  ----------------------
% 5.03/1.98  Preprocessing        : 0.28
% 5.03/1.98  Parsing              : 0.15
% 5.03/1.98  CNF conversion       : 0.02
% 5.03/1.98  Main loop            : 0.94
% 5.03/1.98  Inferencing          : 0.29
% 5.03/1.98  Reduction            : 0.40
% 5.03/1.98  Demodulation         : 0.31
% 5.03/1.98  BG Simplification    : 0.03
% 5.03/1.98  Subsumption          : 0.17
% 5.03/1.98  Abstraction          : 0.04
% 5.03/1.98  MUC search           : 0.00
% 5.03/1.98  Cooper               : 0.00
% 5.03/1.98  Total                : 1.25
% 5.03/1.98  Index Insertion      : 0.00
% 5.03/1.98  Index Deletion       : 0.00
% 5.03/1.98  Index Matching       : 0.00
% 5.03/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
