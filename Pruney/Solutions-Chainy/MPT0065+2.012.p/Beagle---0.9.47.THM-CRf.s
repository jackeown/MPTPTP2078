%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:11 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   39 (  69 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 ( 106 expanded)
%              Number of equality atoms :   14 (  30 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_xboole_0(A,B)
          & r1_tarski(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_10,plain,(
    ! [A_5] : ~ r2_xboole_0(A_5,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_116,plain,(
    ! [A_22,B_23] :
      ( r2_xboole_0(A_22,B_23)
      | B_23 = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_130,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_116,c_16])).

tff(c_131,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_20,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_55,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ r2_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_59,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_55])).

tff(c_18,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_60,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,B_18) = B_18
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_68,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_18,c_60])).

tff(c_79,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_68])).

tff(c_96,plain,(
    ! [A_19,C_20,B_21] :
      ( r1_tarski(A_19,k2_xboole_0(C_20,B_21))
      | ~ r1_tarski(A_19,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_132,plain,(
    ! [A_24] :
      ( r1_tarski(A_24,'#skF_3')
      | ~ r1_tarski(A_24,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_96])).

tff(c_135,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_59,c_132])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_135])).

tff(c_140,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_143,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_140,c_68])).

tff(c_175,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_143])).

tff(c_67,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_59,c_60])).

tff(c_185,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_67])).

tff(c_217,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_20])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:03:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.18  
% 1.87/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.18  %$ r2_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.87/1.18  
% 1.87/1.18  %Foreground sorts:
% 1.87/1.18  
% 1.87/1.18  
% 1.87/1.18  %Background operators:
% 1.87/1.18  
% 1.87/1.18  
% 1.87/1.18  %Foreground operators:
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.18  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.87/1.19  
% 1.87/1.20  tff(f_37, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 1.87/1.20  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.87/1.20  tff(f_34, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.87/1.20  tff(f_52, negated_conjecture, ~(![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_xboole_1)).
% 1.87/1.20  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.87/1.20  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.87/1.20  tff(c_10, plain, (![A_5]: (~r2_xboole_0(A_5, A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.87/1.20  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.87/1.20  tff(c_116, plain, (![A_22, B_23]: (r2_xboole_0(A_22, B_23) | B_23=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.87/1.20  tff(c_16, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.87/1.20  tff(c_130, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_116, c_16])).
% 1.87/1.20  tff(c_131, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_130])).
% 1.87/1.20  tff(c_20, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.87/1.20  tff(c_55, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~r2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.87/1.20  tff(c_59, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_55])).
% 1.87/1.20  tff(c_18, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.87/1.20  tff(c_60, plain, (![A_17, B_18]: (k2_xboole_0(A_17, B_18)=B_18 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.87/1.20  tff(c_68, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_18, c_60])).
% 1.87/1.20  tff(c_79, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2, c_68])).
% 1.87/1.20  tff(c_96, plain, (![A_19, C_20, B_21]: (r1_tarski(A_19, k2_xboole_0(C_20, B_21)) | ~r1_tarski(A_19, B_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.87/1.20  tff(c_132, plain, (![A_24]: (r1_tarski(A_24, '#skF_3') | ~r1_tarski(A_24, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_79, c_96])).
% 1.87/1.20  tff(c_135, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_59, c_132])).
% 1.87/1.20  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_135])).
% 1.87/1.20  tff(c_140, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_130])).
% 1.87/1.20  tff(c_143, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_140, c_68])).
% 1.87/1.20  tff(c_175, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2, c_143])).
% 1.87/1.20  tff(c_67, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_59, c_60])).
% 1.87/1.20  tff(c_185, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_175, c_67])).
% 1.87/1.20  tff(c_217, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_20])).
% 1.87/1.20  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_217])).
% 1.87/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.20  
% 1.87/1.20  Inference rules
% 1.87/1.20  ----------------------
% 1.87/1.20  #Ref     : 0
% 1.87/1.20  #Sup     : 54
% 1.87/1.20  #Fact    : 0
% 1.87/1.20  #Define  : 0
% 1.87/1.20  #Split   : 1
% 1.87/1.20  #Chain   : 0
% 1.87/1.20  #Close   : 0
% 1.87/1.20  
% 1.87/1.20  Ordering : KBO
% 1.87/1.20  
% 1.87/1.20  Simplification rules
% 1.87/1.20  ----------------------
% 1.87/1.20  #Subsume      : 4
% 1.87/1.20  #Demod        : 20
% 1.87/1.20  #Tautology    : 37
% 1.87/1.20  #SimpNegUnit  : 2
% 1.87/1.20  #BackRed      : 10
% 1.87/1.20  
% 1.87/1.20  #Partial instantiations: 0
% 1.87/1.20  #Strategies tried      : 1
% 1.87/1.20  
% 1.87/1.20  Timing (in seconds)
% 1.87/1.20  ----------------------
% 1.87/1.20  Preprocessing        : 0.26
% 1.87/1.20  Parsing              : 0.15
% 1.87/1.20  CNF conversion       : 0.02
% 1.87/1.20  Main loop            : 0.17
% 1.87/1.20  Inferencing          : 0.06
% 1.87/1.20  Reduction            : 0.06
% 1.87/1.20  Demodulation         : 0.04
% 1.87/1.20  BG Simplification    : 0.01
% 1.87/1.20  Subsumption          : 0.03
% 1.87/1.20  Abstraction          : 0.01
% 1.87/1.20  MUC search           : 0.00
% 1.87/1.20  Cooper               : 0.00
% 1.87/1.20  Total                : 0.46
% 1.87/1.20  Index Insertion      : 0.00
% 1.87/1.20  Index Deletion       : 0.00
% 1.87/1.20  Index Matching       : 0.00
% 1.87/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
