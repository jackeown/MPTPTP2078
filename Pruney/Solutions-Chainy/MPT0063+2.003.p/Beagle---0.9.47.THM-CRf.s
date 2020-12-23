%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:09 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   37 (  51 expanded)
%              Number of leaves         :   15 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  77 expanded)
%              Number of equality atoms :   10 (  15 expanded)
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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_xboole_0(A,B)
          & r2_xboole_0(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_xboole_1)).

tff(f_39,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

tff(c_20,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_104,plain,(
    ! [A_21,B_22] :
      ( r2_xboole_0(A_21,B_22)
      | B_22 = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_129,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_16])).

tff(c_133,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_62,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ r2_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_70,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_62])).

tff(c_18,plain,(
    r2_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_69,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_62])).

tff(c_71,plain,(
    ! [A_19,B_20] :
      ( k2_xboole_0(A_19,B_20) = B_20
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_79,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_69,c_71])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_xboole_0(B_4,A_3) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_87,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_4])).

tff(c_136,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_tarski(A_23,k2_xboole_0(C_24,B_25))
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_156,plain,(
    ! [A_26] :
      ( r1_tarski(A_26,'#skF_3')
      | ~ r1_tarski(A_26,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_136])).

tff(c_159,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_156])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_159])).

tff(c_164,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_55,plain,(
    ! [B_15,A_16] :
      ( ~ r2_xboole_0(B_15,A_16)
      | ~ r2_xboole_0(A_16,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_60,plain,(
    ~ r2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_55])).

tff(c_169,plain,(
    ~ r2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_60])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.15  
% 1.80/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.16  %$ r2_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.80/1.16  
% 1.80/1.16  %Foreground sorts:
% 1.80/1.16  
% 1.80/1.16  
% 1.80/1.16  %Background operators:
% 1.80/1.16  
% 1.80/1.16  
% 1.80/1.16  %Foreground operators:
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.80/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.16  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.80/1.16  
% 1.80/1.17  tff(f_54, negated_conjecture, ~(![A, B, C]: ((r2_xboole_0(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_xboole_1)).
% 1.80/1.17  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.80/1.17  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.80/1.17  tff(f_32, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.80/1.17  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.80/1.17  tff(f_30, axiom, (![A, B]: (r2_xboole_0(A, B) => ~r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 1.80/1.17  tff(c_20, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.80/1.17  tff(c_104, plain, (![A_21, B_22]: (r2_xboole_0(A_21, B_22) | B_22=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.80/1.17  tff(c_16, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.80/1.17  tff(c_129, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_104, c_16])).
% 1.80/1.17  tff(c_133, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_129])).
% 1.80/1.17  tff(c_62, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~r2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.80/1.17  tff(c_70, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_62])).
% 1.80/1.17  tff(c_18, plain, (r2_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.80/1.17  tff(c_69, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_62])).
% 1.80/1.17  tff(c_71, plain, (![A_19, B_20]: (k2_xboole_0(A_19, B_20)=B_20 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.80/1.17  tff(c_79, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_69, c_71])).
% 1.80/1.17  tff(c_4, plain, (![B_4, A_3]: (k2_xboole_0(B_4, A_3)=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.80/1.17  tff(c_87, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_79, c_4])).
% 1.80/1.17  tff(c_136, plain, (![A_23, C_24, B_25]: (r1_tarski(A_23, k2_xboole_0(C_24, B_25)) | ~r1_tarski(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.80/1.17  tff(c_156, plain, (![A_26]: (r1_tarski(A_26, '#skF_3') | ~r1_tarski(A_26, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_136])).
% 1.80/1.17  tff(c_159, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_156])).
% 1.80/1.17  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_159])).
% 1.80/1.17  tff(c_164, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_129])).
% 1.80/1.17  tff(c_55, plain, (![B_15, A_16]: (~r2_xboole_0(B_15, A_16) | ~r2_xboole_0(A_16, B_15))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.80/1.17  tff(c_60, plain, (~r2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_55])).
% 1.80/1.17  tff(c_169, plain, (~r2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_60])).
% 1.80/1.17  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_169])).
% 1.80/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.17  
% 1.80/1.17  Inference rules
% 1.80/1.17  ----------------------
% 1.80/1.17  #Ref     : 0
% 1.80/1.17  #Sup     : 37
% 1.80/1.17  #Fact    : 0
% 1.80/1.17  #Define  : 0
% 1.80/1.17  #Split   : 3
% 1.80/1.17  #Chain   : 0
% 1.80/1.17  #Close   : 0
% 1.80/1.17  
% 1.80/1.17  Ordering : KBO
% 1.80/1.17  
% 1.80/1.17  Simplification rules
% 1.80/1.17  ----------------------
% 1.80/1.17  #Subsume      : 0
% 1.80/1.17  #Demod        : 12
% 1.80/1.17  #Tautology    : 21
% 1.80/1.17  #SimpNegUnit  : 1
% 1.80/1.17  #BackRed      : 6
% 1.80/1.17  
% 1.80/1.17  #Partial instantiations: 0
% 1.80/1.17  #Strategies tried      : 1
% 1.80/1.17  
% 1.80/1.17  Timing (in seconds)
% 1.80/1.17  ----------------------
% 1.80/1.17  Preprocessing        : 0.26
% 1.80/1.17  Parsing              : 0.15
% 1.80/1.17  CNF conversion       : 0.02
% 1.80/1.17  Main loop            : 0.16
% 1.80/1.17  Inferencing          : 0.06
% 1.80/1.17  Reduction            : 0.05
% 1.80/1.17  Demodulation         : 0.04
% 1.80/1.17  BG Simplification    : 0.01
% 1.80/1.17  Subsumption          : 0.03
% 1.80/1.17  Abstraction          : 0.01
% 1.80/1.17  MUC search           : 0.00
% 1.88/1.17  Cooper               : 0.00
% 1.88/1.17  Total                : 0.45
% 1.88/1.17  Index Insertion      : 0.00
% 1.88/1.17  Index Deletion       : 0.00
% 1.88/1.17  Index Matching       : 0.00
% 1.88/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
