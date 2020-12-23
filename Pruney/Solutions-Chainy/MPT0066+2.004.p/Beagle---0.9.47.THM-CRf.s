%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:13 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   37 (  68 expanded)
%              Number of leaves         :   14 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :   46 ( 112 expanded)
%              Number of equality atoms :   10 (  21 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r2_xboole_0(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

tff(c_6,plain,(
    ! [B_4] : ~ r2_xboole_0(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_xboole_0(A_3,B_4)
      | B_4 = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    r2_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ r2_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_24])).

tff(c_29,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_37,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_18,c_29])).

tff(c_46,plain,(
    ! [A_17,C_18,B_19] :
      ( r1_tarski(A_17,C_18)
      | ~ r1_tarski(k2_xboole_0(A_17,B_19),C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_53,plain,(
    ! [C_20] :
      ( r1_tarski('#skF_1',C_20)
      | ~ r1_tarski('#skF_2',C_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_46])).

tff(c_57,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_53])).

tff(c_69,plain,(
    ! [A_21,B_22] :
      ( r2_xboole_0(A_21,B_22)
      | B_22 = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_84,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_69,c_14])).

tff(c_92,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_84])).

tff(c_20,plain,(
    ! [B_11,A_12] :
      ( ~ r2_xboole_0(B_11,A_12)
      | ~ r2_xboole_0(A_12,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_23,plain,(
    ~ r2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_20])).

tff(c_97,plain,(
    ~ r2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_23])).

tff(c_127,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_97])).

tff(c_130,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_127])).

tff(c_99,plain,(
    r2_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_16])).

tff(c_132,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_99])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.13  
% 1.72/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.13  %$ r2_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.72/1.13  
% 1.72/1.13  %Foreground sorts:
% 1.72/1.13  
% 1.72/1.13  
% 1.72/1.13  %Background operators:
% 1.72/1.13  
% 1.72/1.13  
% 1.72/1.13  %Foreground operators:
% 1.72/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.13  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.72/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.72/1.13  
% 1.72/1.14  tff(f_37, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.72/1.14  tff(f_52, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_xboole_1)).
% 1.72/1.14  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.72/1.14  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.72/1.14  tff(f_30, axiom, (![A, B]: (r2_xboole_0(A, B) => ~r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 1.72/1.14  tff(c_6, plain, (![B_4]: (~r2_xboole_0(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.72/1.14  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.72/1.14  tff(c_4, plain, (![A_3, B_4]: (r2_xboole_0(A_3, B_4) | B_4=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.72/1.14  tff(c_16, plain, (r2_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.72/1.14  tff(c_24, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~r2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.72/1.14  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_24])).
% 1.72/1.14  tff(c_29, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.72/1.14  tff(c_37, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_18, c_29])).
% 1.72/1.14  tff(c_46, plain, (![A_17, C_18, B_19]: (r1_tarski(A_17, C_18) | ~r1_tarski(k2_xboole_0(A_17, B_19), C_18))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.72/1.14  tff(c_53, plain, (![C_20]: (r1_tarski('#skF_1', C_20) | ~r1_tarski('#skF_2', C_20))), inference(superposition, [status(thm), theory('equality')], [c_37, c_46])).
% 1.72/1.14  tff(c_57, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_53])).
% 1.72/1.14  tff(c_69, plain, (![A_21, B_22]: (r2_xboole_0(A_21, B_22) | B_22=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.72/1.14  tff(c_14, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.72/1.14  tff(c_84, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_69, c_14])).
% 1.72/1.14  tff(c_92, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_84])).
% 1.72/1.14  tff(c_20, plain, (![B_11, A_12]: (~r2_xboole_0(B_11, A_12) | ~r2_xboole_0(A_12, B_11))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.72/1.14  tff(c_23, plain, (~r2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_20])).
% 1.72/1.14  tff(c_97, plain, (~r2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_23])).
% 1.72/1.14  tff(c_127, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4, c_97])).
% 1.72/1.14  tff(c_130, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_127])).
% 1.72/1.14  tff(c_99, plain, (r2_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_16])).
% 1.72/1.14  tff(c_132, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_99])).
% 1.72/1.14  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_132])).
% 1.72/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.14  
% 1.72/1.14  Inference rules
% 1.72/1.14  ----------------------
% 1.72/1.14  #Ref     : 0
% 1.72/1.14  #Sup     : 28
% 1.72/1.14  #Fact    : 0
% 1.72/1.14  #Define  : 0
% 1.72/1.14  #Split   : 0
% 1.72/1.14  #Chain   : 0
% 1.72/1.14  #Close   : 0
% 1.72/1.14  
% 1.72/1.14  Ordering : KBO
% 1.72/1.14  
% 1.72/1.14  Simplification rules
% 1.72/1.14  ----------------------
% 1.72/1.14  #Subsume      : 2
% 1.72/1.14  #Demod        : 20
% 1.72/1.14  #Tautology    : 13
% 1.72/1.14  #SimpNegUnit  : 1
% 1.72/1.14  #BackRed      : 12
% 1.72/1.14  
% 1.72/1.14  #Partial instantiations: 0
% 1.72/1.14  #Strategies tried      : 1
% 1.72/1.14  
% 1.72/1.14  Timing (in seconds)
% 1.72/1.14  ----------------------
% 1.72/1.14  Preprocessing        : 0.25
% 1.72/1.14  Parsing              : 0.14
% 1.72/1.14  CNF conversion       : 0.02
% 1.72/1.14  Main loop            : 0.13
% 1.72/1.14  Inferencing          : 0.05
% 1.72/1.14  Reduction            : 0.04
% 1.72/1.14  Demodulation         : 0.03
% 1.72/1.14  BG Simplification    : 0.01
% 1.72/1.14  Subsumption          : 0.02
% 1.72/1.14  Abstraction          : 0.01
% 1.72/1.14  MUC search           : 0.00
% 1.72/1.15  Cooper               : 0.00
% 1.72/1.15  Total                : 0.40
% 1.72/1.15  Index Insertion      : 0.00
% 1.72/1.15  Index Deletion       : 0.00
% 1.72/1.15  Index Matching       : 0.00
% 1.72/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
