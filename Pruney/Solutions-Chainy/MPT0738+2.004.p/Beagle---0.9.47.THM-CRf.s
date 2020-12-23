%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:04 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   44 (  77 expanded)
%              Number of leaves         :   19 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 174 expanded)
%              Number of equality atoms :    6 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r1_ordinal1(A,B)
              | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_38,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_68,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_26,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_52,plain,(
    ! [A_23,B_24] :
      ( r2_hidden('#skF_1'(A_23,B_24),A_23)
      | r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,(
    ! [A_23] : r1_tarski(A_23,A_23) ),
    inference(resolution,[status(thm)],[c_52,c_4])).

tff(c_89,plain,(
    ! [A_35,B_36] :
      ( r1_ordinal1(A_35,B_36)
      | ~ r1_tarski(A_35,B_36)
      | ~ v3_ordinal1(B_36)
      | ~ v3_ordinal1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_97,plain,(
    ! [A_23] :
      ( r1_ordinal1(A_23,A_23)
      | ~ v3_ordinal1(A_23) ) ),
    inference(resolution,[status(thm)],[c_57,c_89])).

tff(c_31,plain,(
    ! [A_17] :
      ( v1_ordinal1(A_17)
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_31])).

tff(c_145,plain,(
    ! [B_45,A_46] :
      ( r2_hidden(B_45,A_46)
      | B_45 = A_46
      | r2_hidden(A_46,B_45)
      | ~ v3_ordinal1(B_45)
      | ~ v3_ordinal1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [B_10,A_7] :
      ( r1_tarski(B_10,A_7)
      | ~ r2_hidden(B_10,A_7)
      | ~ v1_ordinal1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_172,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ v1_ordinal1(B_48)
      | r2_hidden(B_48,A_47)
      | B_48 = A_47
      | ~ v3_ordinal1(B_48)
      | ~ v3_ordinal1(A_47) ) ),
    inference(resolution,[status(thm)],[c_145,c_12])).

tff(c_24,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_184,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ v1_ordinal1('#skF_4')
    | '#skF_3' = '#skF_4'
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_172,c_24])).

tff(c_190,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_38,c_184])).

tff(c_191,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_194,plain,(
    ~ r1_ordinal1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_26])).

tff(c_206,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_97,c_194])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_206])).

tff(c_211,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( r1_ordinal1(A_11,B_12)
      | ~ r1_tarski(A_11,B_12)
      | ~ v3_ordinal1(B_12)
      | ~ v3_ordinal1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_215,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_211,c_18])).

tff(c_218,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_215])).

tff(c_220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_218])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:54:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.24  
% 1.94/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.24  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.94/1.24  
% 1.94/1.24  %Foreground sorts:
% 1.94/1.24  
% 1.94/1.24  
% 1.94/1.24  %Background operators:
% 1.94/1.24  
% 1.94/1.24  
% 1.94/1.24  %Foreground operators:
% 1.94/1.24  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.94/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.24  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 1.94/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.24  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 1.94/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.24  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.94/1.24  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 1.94/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.24  tff('#skF_4', type, '#skF_4': $i).
% 1.94/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.94/1.24  
% 1.94/1.25  tff(f_78, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 1.94/1.25  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.94/1.25  tff(f_53, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 1.94/1.25  tff(f_38, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 1.94/1.25  tff(f_68, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 1.94/1.25  tff(f_45, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 1.94/1.25  tff(c_26, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.94/1.25  tff(c_30, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.94/1.25  tff(c_28, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.94/1.25  tff(c_52, plain, (![A_23, B_24]: (r2_hidden('#skF_1'(A_23, B_24), A_23) | r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.94/1.25  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.94/1.25  tff(c_57, plain, (![A_23]: (r1_tarski(A_23, A_23))), inference(resolution, [status(thm)], [c_52, c_4])).
% 1.94/1.25  tff(c_89, plain, (![A_35, B_36]: (r1_ordinal1(A_35, B_36) | ~r1_tarski(A_35, B_36) | ~v3_ordinal1(B_36) | ~v3_ordinal1(A_35))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.94/1.25  tff(c_97, plain, (![A_23]: (r1_ordinal1(A_23, A_23) | ~v3_ordinal1(A_23))), inference(resolution, [status(thm)], [c_57, c_89])).
% 1.94/1.25  tff(c_31, plain, (![A_17]: (v1_ordinal1(A_17) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.94/1.25  tff(c_38, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_31])).
% 1.94/1.25  tff(c_145, plain, (![B_45, A_46]: (r2_hidden(B_45, A_46) | B_45=A_46 | r2_hidden(A_46, B_45) | ~v3_ordinal1(B_45) | ~v3_ordinal1(A_46))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.94/1.25  tff(c_12, plain, (![B_10, A_7]: (r1_tarski(B_10, A_7) | ~r2_hidden(B_10, A_7) | ~v1_ordinal1(A_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.25  tff(c_172, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~v1_ordinal1(B_48) | r2_hidden(B_48, A_47) | B_48=A_47 | ~v3_ordinal1(B_48) | ~v3_ordinal1(A_47))), inference(resolution, [status(thm)], [c_145, c_12])).
% 1.94/1.25  tff(c_24, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.94/1.25  tff(c_184, plain, (r1_tarski('#skF_3', '#skF_4') | ~v1_ordinal1('#skF_4') | '#skF_3'='#skF_4' | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_172, c_24])).
% 1.94/1.25  tff(c_190, plain, (r1_tarski('#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_38, c_184])).
% 1.94/1.25  tff(c_191, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_190])).
% 1.94/1.25  tff(c_194, plain, (~r1_ordinal1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_191, c_26])).
% 1.94/1.25  tff(c_206, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_97, c_194])).
% 1.94/1.25  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_206])).
% 1.94/1.25  tff(c_211, plain, (r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_190])).
% 1.94/1.25  tff(c_18, plain, (![A_11, B_12]: (r1_ordinal1(A_11, B_12) | ~r1_tarski(A_11, B_12) | ~v3_ordinal1(B_12) | ~v3_ordinal1(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.94/1.25  tff(c_215, plain, (r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_211, c_18])).
% 1.94/1.25  tff(c_218, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_215])).
% 1.94/1.25  tff(c_220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_218])).
% 1.94/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.25  
% 1.94/1.25  Inference rules
% 1.94/1.25  ----------------------
% 1.94/1.25  #Ref     : 0
% 1.94/1.25  #Sup     : 34
% 1.94/1.25  #Fact    : 2
% 1.94/1.25  #Define  : 0
% 1.94/1.25  #Split   : 1
% 1.94/1.25  #Chain   : 0
% 1.94/1.25  #Close   : 0
% 1.94/1.25  
% 1.94/1.25  Ordering : KBO
% 1.94/1.25  
% 1.94/1.25  Simplification rules
% 1.94/1.25  ----------------------
% 1.94/1.25  #Subsume      : 1
% 1.94/1.25  #Demod        : 15
% 1.94/1.25  #Tautology    : 11
% 1.94/1.25  #SimpNegUnit  : 1
% 1.94/1.25  #BackRed      : 5
% 1.94/1.25  
% 1.94/1.25  #Partial instantiations: 0
% 1.94/1.25  #Strategies tried      : 1
% 1.94/1.25  
% 1.94/1.25  Timing (in seconds)
% 1.94/1.25  ----------------------
% 1.94/1.26  Preprocessing        : 0.28
% 1.94/1.26  Parsing              : 0.15
% 1.94/1.26  CNF conversion       : 0.02
% 1.94/1.26  Main loop            : 0.21
% 1.94/1.26  Inferencing          : 0.09
% 1.94/1.26  Reduction            : 0.05
% 1.94/1.26  Demodulation         : 0.04
% 1.94/1.26  BG Simplification    : 0.02
% 1.94/1.26  Subsumption          : 0.04
% 1.94/1.26  Abstraction          : 0.01
% 1.94/1.26  MUC search           : 0.00
% 1.94/1.26  Cooper               : 0.00
% 1.94/1.26  Total                : 0.52
% 1.94/1.26  Index Insertion      : 0.00
% 1.94/1.26  Index Deletion       : 0.00
% 1.94/1.26  Index Matching       : 0.00
% 1.94/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
