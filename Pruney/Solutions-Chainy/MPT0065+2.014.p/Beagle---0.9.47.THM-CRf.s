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
% DateTime   : Thu Dec  3 09:43:12 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   38 (  63 expanded)
%              Number of leaves         :   15 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 ( 100 expanded)
%              Number of equality atoms :   13 (  24 expanded)
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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_xboole_0(A,B)
          & r1_tarski(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_10,plain,(
    ! [A_5] : ~ r2_xboole_0(A_5,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_96,plain,(
    ! [A_19,B_20] :
      ( r2_xboole_0(A_19,B_20)
      | B_20 = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_110,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_16])).

tff(c_118,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_20,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

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
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_111,plain,(
    ! [A_21,C_22,B_23] :
      ( r1_tarski(A_21,C_22)
      | ~ r1_tarski(B_23,C_22)
      | ~ r1_tarski(A_21,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_119,plain,(
    ! [A_24] :
      ( r1_tarski(A_24,'#skF_3')
      | ~ r1_tarski(A_24,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_111])).

tff(c_122,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_59,c_119])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_122])).

tff(c_127,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_60,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,B_18) = B_18
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_68,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_18,c_60])).

tff(c_136,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_127,c_68])).

tff(c_172,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_136])).

tff(c_67,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_59,c_60])).

tff(c_185,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_67])).

tff(c_195,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_20])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.29  
% 1.92/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.29  %$ r2_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.92/1.29  
% 1.92/1.29  %Foreground sorts:
% 1.92/1.29  
% 1.92/1.29  
% 1.92/1.29  %Background operators:
% 1.92/1.29  
% 1.92/1.29  
% 1.92/1.29  %Foreground operators:
% 1.92/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.29  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.29  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.29  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.29  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.92/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.92/1.29  
% 1.92/1.30  tff(f_37, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 1.92/1.30  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.92/1.30  tff(f_34, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.92/1.30  tff(f_54, negated_conjecture, ~(![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_xboole_1)).
% 1.92/1.30  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.92/1.30  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.92/1.30  tff(c_10, plain, (![A_5]: (~r2_xboole_0(A_5, A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.92/1.30  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.92/1.30  tff(c_96, plain, (![A_19, B_20]: (r2_xboole_0(A_19, B_20) | B_20=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.92/1.30  tff(c_16, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.92/1.30  tff(c_110, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_96, c_16])).
% 1.92/1.30  tff(c_118, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_110])).
% 1.92/1.30  tff(c_20, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.92/1.30  tff(c_55, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~r2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.92/1.30  tff(c_59, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_55])).
% 1.92/1.30  tff(c_18, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.92/1.30  tff(c_111, plain, (![A_21, C_22, B_23]: (r1_tarski(A_21, C_22) | ~r1_tarski(B_23, C_22) | ~r1_tarski(A_21, B_23))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.92/1.30  tff(c_119, plain, (![A_24]: (r1_tarski(A_24, '#skF_3') | ~r1_tarski(A_24, '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_111])).
% 1.92/1.30  tff(c_122, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_59, c_119])).
% 1.92/1.30  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_122])).
% 1.92/1.30  tff(c_127, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_110])).
% 1.92/1.30  tff(c_60, plain, (![A_17, B_18]: (k2_xboole_0(A_17, B_18)=B_18 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.92/1.30  tff(c_68, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_18, c_60])).
% 1.92/1.30  tff(c_136, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_127, c_68])).
% 1.92/1.30  tff(c_172, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2, c_136])).
% 1.92/1.30  tff(c_67, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_59, c_60])).
% 1.92/1.30  tff(c_185, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_67])).
% 1.92/1.30  tff(c_195, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_20])).
% 1.92/1.30  tff(c_201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_195])).
% 1.92/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.30  
% 1.92/1.30  Inference rules
% 1.92/1.30  ----------------------
% 1.92/1.30  #Ref     : 0
% 1.92/1.30  #Sup     : 45
% 1.92/1.30  #Fact    : 0
% 1.92/1.30  #Define  : 0
% 1.92/1.30  #Split   : 1
% 1.92/1.30  #Chain   : 0
% 1.92/1.30  #Close   : 0
% 1.92/1.30  
% 1.92/1.30  Ordering : KBO
% 1.92/1.30  
% 1.92/1.30  Simplification rules
% 1.92/1.30  ----------------------
% 1.92/1.30  #Subsume      : 2
% 1.92/1.30  #Demod        : 25
% 1.92/1.30  #Tautology    : 35
% 1.92/1.30  #SimpNegUnit  : 2
% 1.92/1.30  #BackRed      : 11
% 1.92/1.30  
% 1.92/1.30  #Partial instantiations: 0
% 1.92/1.30  #Strategies tried      : 1
% 1.92/1.30  
% 1.92/1.30  Timing (in seconds)
% 1.92/1.30  ----------------------
% 1.92/1.30  Preprocessing        : 0.28
% 1.92/1.30  Parsing              : 0.15
% 1.92/1.30  CNF conversion       : 0.02
% 1.92/1.30  Main loop            : 0.16
% 1.92/1.30  Inferencing          : 0.06
% 1.92/1.30  Reduction            : 0.05
% 1.92/1.30  Demodulation         : 0.04
% 1.92/1.30  BG Simplification    : 0.01
% 1.92/1.30  Subsumption          : 0.03
% 1.92/1.30  Abstraction          : 0.01
% 1.92/1.30  MUC search           : 0.00
% 1.92/1.30  Cooper               : 0.00
% 1.92/1.30  Total                : 0.47
% 1.92/1.30  Index Insertion      : 0.00
% 1.92/1.31  Index Deletion       : 0.00
% 1.92/1.31  Index Matching       : 0.00
% 1.92/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
