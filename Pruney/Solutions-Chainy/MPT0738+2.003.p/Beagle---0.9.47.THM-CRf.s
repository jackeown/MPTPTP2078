%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:04 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   41 (  73 expanded)
%              Number of leaves         :   18 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 ( 167 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r1_ordinal1(A,B)
              | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_37,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_67,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_26,plain,(
    ~ r1_ordinal1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [A_23,B_24] :
      ( r1_ordinal1(A_23,B_24)
      | ~ r1_tarski(A_23,B_24)
      | ~ v3_ordinal1(B_24)
      | ~ v3_ordinal1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_69,plain,(
    ! [B_2] :
      ( r1_ordinal1(B_2,B_2)
      | ~ v3_ordinal1(B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_42,plain,(
    ! [A_16] :
      ( v1_ordinal1(A_16)
      | ~ v3_ordinal1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_49,plain,(
    v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_42])).

tff(c_100,plain,(
    ! [B_28,A_29] :
      ( r2_hidden(B_28,A_29)
      | B_28 = A_29
      | r2_hidden(A_29,B_28)
      | ~ v3_ordinal1(B_28)
      | ~ v3_ordinal1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12,plain,(
    ! [B_7,A_4] :
      ( r1_tarski(B_7,A_4)
      | ~ r2_hidden(B_7,A_4)
      | ~ v1_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_126,plain,(
    ! [B_34,A_35] :
      ( r1_tarski(B_34,A_35)
      | ~ v1_ordinal1(A_35)
      | B_34 = A_35
      | r2_hidden(A_35,B_34)
      | ~ v3_ordinal1(B_34)
      | ~ v3_ordinal1(A_35) ) ),
    inference(resolution,[status(thm)],[c_100,c_12])).

tff(c_24,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_132,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ v1_ordinal1('#skF_3')
    | '#skF_2' = '#skF_3'
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_126,c_24])).

tff(c_136,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_49,c_132])).

tff(c_137,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_140,plain,(
    ~ r1_ordinal1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_26])).

tff(c_152,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_69,c_140])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_152])).

tff(c_157,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( r1_ordinal1(A_8,B_9)
      | ~ r1_tarski(A_8,B_9)
      | ~ v3_ordinal1(B_9)
      | ~ v3_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_164,plain,
    ( r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_157,c_18])).

tff(c_173,plain,(
    r1_ordinal1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_164])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:31:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.29  
% 1.90/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.29  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3
% 1.90/1.29  
% 1.90/1.29  %Foreground sorts:
% 1.90/1.29  
% 1.90/1.29  
% 1.90/1.29  %Background operators:
% 1.90/1.29  
% 1.90/1.29  
% 1.90/1.29  %Foreground operators:
% 1.90/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.29  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 1.90/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.90/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.29  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 1.90/1.29  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.29  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.29  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.90/1.29  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 1.90/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.29  
% 1.90/1.31  tff(f_77, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 1.90/1.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.90/1.31  tff(f_52, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 1.90/1.31  tff(f_37, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 1.90/1.31  tff(f_67, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 1.90/1.31  tff(f_44, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 1.90/1.31  tff(c_26, plain, (~r1_ordinal1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.90/1.31  tff(c_30, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.90/1.31  tff(c_28, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.90/1.31  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.90/1.31  tff(c_65, plain, (![A_23, B_24]: (r1_ordinal1(A_23, B_24) | ~r1_tarski(A_23, B_24) | ~v3_ordinal1(B_24) | ~v3_ordinal1(A_23))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.31  tff(c_69, plain, (![B_2]: (r1_ordinal1(B_2, B_2) | ~v3_ordinal1(B_2))), inference(resolution, [status(thm)], [c_6, c_65])).
% 1.90/1.31  tff(c_42, plain, (![A_16]: (v1_ordinal1(A_16) | ~v3_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.90/1.31  tff(c_49, plain, (v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_42])).
% 1.90/1.31  tff(c_100, plain, (![B_28, A_29]: (r2_hidden(B_28, A_29) | B_28=A_29 | r2_hidden(A_29, B_28) | ~v3_ordinal1(B_28) | ~v3_ordinal1(A_29))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.90/1.31  tff(c_12, plain, (![B_7, A_4]: (r1_tarski(B_7, A_4) | ~r2_hidden(B_7, A_4) | ~v1_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.90/1.31  tff(c_126, plain, (![B_34, A_35]: (r1_tarski(B_34, A_35) | ~v1_ordinal1(A_35) | B_34=A_35 | r2_hidden(A_35, B_34) | ~v3_ordinal1(B_34) | ~v3_ordinal1(A_35))), inference(resolution, [status(thm)], [c_100, c_12])).
% 1.90/1.31  tff(c_24, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.90/1.31  tff(c_132, plain, (r1_tarski('#skF_2', '#skF_3') | ~v1_ordinal1('#skF_3') | '#skF_2'='#skF_3' | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_126, c_24])).
% 1.90/1.31  tff(c_136, plain, (r1_tarski('#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_49, c_132])).
% 1.90/1.31  tff(c_137, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_136])).
% 1.90/1.31  tff(c_140, plain, (~r1_ordinal1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_26])).
% 1.90/1.31  tff(c_152, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_69, c_140])).
% 1.90/1.31  tff(c_156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_152])).
% 1.90/1.31  tff(c_157, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_136])).
% 1.90/1.31  tff(c_18, plain, (![A_8, B_9]: (r1_ordinal1(A_8, B_9) | ~r1_tarski(A_8, B_9) | ~v3_ordinal1(B_9) | ~v3_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.31  tff(c_164, plain, (r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_157, c_18])).
% 1.90/1.31  tff(c_173, plain, (r1_ordinal1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_164])).
% 1.90/1.31  tff(c_175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_173])).
% 1.90/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.31  
% 1.90/1.31  Inference rules
% 1.90/1.31  ----------------------
% 1.90/1.31  #Ref     : 0
% 1.90/1.31  #Sup     : 23
% 1.90/1.31  #Fact    : 2
% 1.90/1.31  #Define  : 0
% 1.90/1.31  #Split   : 1
% 1.90/1.31  #Chain   : 0
% 1.90/1.31  #Close   : 0
% 1.90/1.31  
% 1.90/1.31  Ordering : KBO
% 1.90/1.31  
% 1.90/1.31  Simplification rules
% 1.90/1.31  ----------------------
% 1.90/1.31  #Subsume      : 2
% 1.90/1.31  #Demod        : 18
% 1.90/1.31  #Tautology    : 13
% 1.90/1.31  #SimpNegUnit  : 2
% 1.90/1.31  #BackRed      : 5
% 1.90/1.31  
% 1.90/1.31  #Partial instantiations: 0
% 1.90/1.31  #Strategies tried      : 1
% 1.90/1.31  
% 1.90/1.31  Timing (in seconds)
% 1.90/1.31  ----------------------
% 1.90/1.32  Preprocessing        : 0.28
% 1.90/1.32  Parsing              : 0.15
% 1.90/1.32  CNF conversion       : 0.02
% 1.90/1.32  Main loop            : 0.21
% 1.90/1.32  Inferencing          : 0.08
% 1.90/1.32  Reduction            : 0.05
% 1.90/1.32  Demodulation         : 0.04
% 1.90/1.32  BG Simplification    : 0.01
% 1.90/1.32  Subsumption          : 0.05
% 1.90/1.32  Abstraction          : 0.01
% 1.90/1.32  MUC search           : 0.00
% 1.90/1.32  Cooper               : 0.00
% 1.90/1.32  Total                : 0.53
% 1.90/1.32  Index Insertion      : 0.00
% 1.90/1.32  Index Deletion       : 0.00
% 1.90/1.32  Index Matching       : 0.00
% 1.90/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
