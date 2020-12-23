%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:12 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   44 (  64 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  92 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_xboole_0(A,B)
          & r1_tarski(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_8,plain,(
    ! [A_3] : ~ r2_xboole_0(A_3,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_37,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ r2_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_41,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_37])).

tff(c_64,plain,(
    ! [A_23,B_24] :
      ( k2_xboole_0(A_23,B_24) = B_24
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_75,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_41,c_64])).

tff(c_102,plain,(
    ! [A_27,B_28] :
      ( r2_xboole_0(A_27,B_28)
      | B_28 = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_114,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_22])).

tff(c_125,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_24,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_130,plain,(
    ! [A_29,C_30,B_31] :
      ( r1_tarski(A_29,C_30)
      | ~ r1_tarski(k2_xboole_0(A_29,B_31),C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_163,plain,(
    ! [C_33] :
      ( r1_tarski('#skF_1',C_33)
      | ~ r1_tarski('#skF_2',C_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_130])).

tff(c_173,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_163])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_173])).

tff(c_180,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_42,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_42])).

tff(c_184,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_50])).

tff(c_20,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_229,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_20])).

tff(c_232,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_75,c_229])).

tff(c_248,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_26])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.24  
% 2.05/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.24  %$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.05/1.24  
% 2.05/1.24  %Foreground sorts:
% 2.05/1.24  
% 2.05/1.24  
% 2.05/1.24  %Background operators:
% 2.05/1.24  
% 2.05/1.24  
% 2.05/1.24  %Foreground operators:
% 2.05/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.05/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.24  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.05/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.05/1.24  
% 2.05/1.26  tff(f_35, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 2.05/1.26  tff(f_49, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.05/1.26  tff(f_58, negated_conjecture, ~(![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_xboole_1)).
% 2.05/1.26  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.05/1.26  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.05/1.26  tff(f_43, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.05/1.26  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.05/1.26  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.05/1.26  tff(c_8, plain, (![A_3]: (~r2_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.26  tff(c_18, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.05/1.26  tff(c_26, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.26  tff(c_37, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~r2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.05/1.26  tff(c_41, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_37])).
% 2.05/1.26  tff(c_64, plain, (![A_23, B_24]: (k2_xboole_0(A_23, B_24)=B_24 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.05/1.26  tff(c_75, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_41, c_64])).
% 2.05/1.26  tff(c_102, plain, (![A_27, B_28]: (r2_xboole_0(A_27, B_28) | B_28=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.05/1.26  tff(c_22, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.26  tff(c_114, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_102, c_22])).
% 2.05/1.26  tff(c_125, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_114])).
% 2.05/1.26  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.26  tff(c_130, plain, (![A_29, C_30, B_31]: (r1_tarski(A_29, C_30) | ~r1_tarski(k2_xboole_0(A_29, B_31), C_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.05/1.26  tff(c_163, plain, (![C_33]: (r1_tarski('#skF_1', C_33) | ~r1_tarski('#skF_2', C_33))), inference(superposition, [status(thm), theory('equality')], [c_75, c_130])).
% 2.05/1.26  tff(c_173, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_163])).
% 2.05/1.26  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_173])).
% 2.05/1.26  tff(c_180, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_114])).
% 2.05/1.26  tff(c_42, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.05/1.26  tff(c_50, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_42])).
% 2.05/1.26  tff(c_184, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_180, c_50])).
% 2.05/1.26  tff(c_20, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.26  tff(c_229, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_184, c_20])).
% 2.05/1.26  tff(c_232, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_75, c_229])).
% 2.05/1.26  tff(c_248, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_232, c_26])).
% 2.05/1.26  tff(c_252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_248])).
% 2.05/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.26  
% 2.05/1.26  Inference rules
% 2.05/1.26  ----------------------
% 2.05/1.26  #Ref     : 0
% 2.05/1.26  #Sup     : 58
% 2.05/1.26  #Fact    : 0
% 2.05/1.26  #Define  : 0
% 2.05/1.26  #Split   : 1
% 2.05/1.26  #Chain   : 0
% 2.05/1.26  #Close   : 0
% 2.05/1.26  
% 2.05/1.26  Ordering : KBO
% 2.05/1.26  
% 2.05/1.26  Simplification rules
% 2.05/1.26  ----------------------
% 2.05/1.26  #Subsume      : 4
% 2.05/1.26  #Demod        : 23
% 2.05/1.26  #Tautology    : 32
% 2.05/1.26  #SimpNegUnit  : 2
% 2.05/1.26  #BackRed      : 13
% 2.05/1.26  
% 2.05/1.26  #Partial instantiations: 0
% 2.05/1.26  #Strategies tried      : 1
% 2.05/1.26  
% 2.05/1.26  Timing (in seconds)
% 2.05/1.26  ----------------------
% 2.05/1.26  Preprocessing        : 0.28
% 2.05/1.26  Parsing              : 0.16
% 2.05/1.26  CNF conversion       : 0.02
% 2.05/1.26  Main loop            : 0.20
% 2.05/1.26  Inferencing          : 0.08
% 2.05/1.26  Reduction            : 0.06
% 2.05/1.26  Demodulation         : 0.04
% 2.05/1.26  BG Simplification    : 0.01
% 2.05/1.26  Subsumption          : 0.03
% 2.05/1.26  Abstraction          : 0.01
% 2.05/1.26  MUC search           : 0.00
% 2.05/1.26  Cooper               : 0.00
% 2.05/1.26  Total                : 0.51
% 2.05/1.26  Index Insertion      : 0.00
% 2.05/1.26  Index Deletion       : 0.00
% 2.05/1.26  Index Matching       : 0.00
% 2.05/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
