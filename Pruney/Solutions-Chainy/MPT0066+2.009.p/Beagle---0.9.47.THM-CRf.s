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
% DateTime   : Thu Dec  3 09:43:14 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   39 (  76 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 ( 120 expanded)
%              Number of equality atoms :   13 (  34 expanded)
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
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r2_xboole_0(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_10,plain,(
    ! [A_5] : ~ r2_xboole_0(A_5,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_96,plain,(
    ! [A_19,B_20] :
      ( r2_xboole_0(A_19,B_20)
      | B_20 = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_110,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_16])).

tff(c_131,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    r2_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_55,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ r2_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_59,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_55])).

tff(c_60,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,B_18) = B_18
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_67,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_59,c_60])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_2])).

tff(c_111,plain,(
    ! [A_21,C_22,B_23] :
      ( r1_tarski(A_21,k2_xboole_0(C_22,B_23))
      | ~ r1_tarski(A_21,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_132,plain,(
    ! [A_24] :
      ( r1_tarski(A_24,'#skF_3')
      | ~ r1_tarski(A_24,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_111])).

tff(c_135,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_132])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_135])).

tff(c_140,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_142,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_140,c_76])).

tff(c_68,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_60])).

tff(c_212,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_68])).

tff(c_146,plain,(
    r2_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_18])).

tff(c_225,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_146])).

tff(c_231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_225])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:00:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.19  %$ r2_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.88/1.19  
% 1.88/1.19  %Foreground sorts:
% 1.88/1.19  
% 1.88/1.19  
% 1.88/1.19  %Background operators:
% 1.88/1.19  
% 1.88/1.19  
% 1.88/1.19  %Foreground operators:
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.19  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.88/1.19  
% 1.88/1.20  tff(f_37, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 1.88/1.20  tff(f_34, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.88/1.20  tff(f_52, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_xboole_1)).
% 1.88/1.20  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.88/1.20  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.88/1.20  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.88/1.20  tff(c_10, plain, (![A_5]: (~r2_xboole_0(A_5, A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.88/1.20  tff(c_96, plain, (![A_19, B_20]: (r2_xboole_0(A_19, B_20) | B_20=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.88/1.20  tff(c_16, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.88/1.20  tff(c_110, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_96, c_16])).
% 1.88/1.20  tff(c_131, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_110])).
% 1.88/1.20  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.88/1.20  tff(c_18, plain, (r2_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.88/1.20  tff(c_55, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~r2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.88/1.20  tff(c_59, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_55])).
% 1.88/1.20  tff(c_60, plain, (![A_17, B_18]: (k2_xboole_0(A_17, B_18)=B_18 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.88/1.20  tff(c_67, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_59, c_60])).
% 1.88/1.20  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.88/1.20  tff(c_76, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_67, c_2])).
% 1.88/1.20  tff(c_111, plain, (![A_21, C_22, B_23]: (r1_tarski(A_21, k2_xboole_0(C_22, B_23)) | ~r1_tarski(A_21, B_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.88/1.20  tff(c_132, plain, (![A_24]: (r1_tarski(A_24, '#skF_3') | ~r1_tarski(A_24, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_111])).
% 1.88/1.20  tff(c_135, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_132])).
% 1.88/1.20  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_135])).
% 1.88/1.20  tff(c_140, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_110])).
% 1.88/1.20  tff(c_142, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_140, c_76])).
% 1.88/1.20  tff(c_68, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_20, c_60])).
% 1.88/1.20  tff(c_212, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_68])).
% 1.88/1.20  tff(c_146, plain, (r2_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_18])).
% 1.88/1.20  tff(c_225, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_212, c_146])).
% 1.88/1.20  tff(c_231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_225])).
% 1.88/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.20  
% 1.88/1.20  Inference rules
% 1.88/1.20  ----------------------
% 1.88/1.20  #Ref     : 0
% 1.88/1.20  #Sup     : 56
% 1.88/1.20  #Fact    : 0
% 1.88/1.20  #Define  : 0
% 1.88/1.20  #Split   : 1
% 1.88/1.20  #Chain   : 0
% 1.88/1.20  #Close   : 0
% 1.88/1.20  
% 1.88/1.20  Ordering : KBO
% 1.88/1.20  
% 1.88/1.20  Simplification rules
% 1.88/1.20  ----------------------
% 1.88/1.20  #Subsume      : 4
% 1.88/1.20  #Demod        : 21
% 1.88/1.20  #Tautology    : 37
% 1.88/1.20  #SimpNegUnit  : 2
% 1.88/1.20  #BackRed      : 11
% 1.88/1.20  
% 1.88/1.20  #Partial instantiations: 0
% 1.88/1.20  #Strategies tried      : 1
% 1.88/1.20  
% 1.88/1.20  Timing (in seconds)
% 1.88/1.20  ----------------------
% 1.88/1.20  Preprocessing        : 0.26
% 1.88/1.20  Parsing              : 0.14
% 1.88/1.20  CNF conversion       : 0.02
% 1.88/1.20  Main loop            : 0.18
% 1.88/1.20  Inferencing          : 0.07
% 1.88/1.20  Reduction            : 0.06
% 1.88/1.20  Demodulation         : 0.04
% 1.88/1.20  BG Simplification    : 0.01
% 1.88/1.21  Subsumption          : 0.03
% 1.88/1.21  Abstraction          : 0.01
% 1.88/1.21  MUC search           : 0.00
% 1.88/1.21  Cooper               : 0.00
% 1.88/1.21  Total                : 0.46
% 1.88/1.21  Index Insertion      : 0.00
% 1.88/1.21  Index Deletion       : 0.00
% 1.88/1.21  Index Matching       : 0.00
% 1.88/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
