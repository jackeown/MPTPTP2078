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
% DateTime   : Thu Dec  3 10:06:31 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   37 (  55 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   67 ( 128 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ~ ( ~ r2_xboole_0(A,B)
                & A != B
                & ~ r2_xboole_0(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_60,axiom,(
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

tff(c_22,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_51,plain,(
    ! [A_19,B_20] :
      ( r2_xboole_0(A_19,B_20)
      | B_20 = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ~ r2_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_64,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_51,c_20])).

tff(c_73,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_64])).

tff(c_28,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_39,plain,(
    ! [A_14] :
      ( v1_ordinal1(A_14)
      | ~ v3_ordinal1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_47,plain,(
    v1_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_39])).

tff(c_46,plain,(
    v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_39])).

tff(c_95,plain,(
    ! [B_23,A_24] :
      ( r2_hidden(B_23,A_24)
      | B_23 = A_24
      | r2_hidden(A_24,B_23)
      | ~ v3_ordinal1(B_23)
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [B_7,A_4] :
      ( r1_tarski(B_7,A_4)
      | ~ r2_hidden(B_7,A_4)
      | ~ v1_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_104,plain,(
    ! [B_25,A_26] :
      ( r1_tarski(B_25,A_26)
      | ~ v1_ordinal1(A_26)
      | B_25 = A_26
      | r2_hidden(A_26,B_25)
      | ~ v3_ordinal1(B_25)
      | ~ v3_ordinal1(A_26) ) ),
    inference(resolution,[status(thm)],[c_95,c_12])).

tff(c_125,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | ~ v1_ordinal1(B_28)
      | r1_tarski(B_28,A_27)
      | ~ v1_ordinal1(A_27)
      | B_28 = A_27
      | ~ v3_ordinal1(B_28)
      | ~ v3_ordinal1(A_27) ) ),
    inference(resolution,[status(thm)],[c_104,c_12])).

tff(c_24,plain,(
    ~ r2_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_61,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_24])).

tff(c_70,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_61])).

tff(c_129,plain,
    ( ~ v1_ordinal1('#skF_3')
    | r1_tarski('#skF_3','#skF_2')
    | ~ v1_ordinal1('#skF_2')
    | '#skF_2' = '#skF_3'
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_125,c_70])).

tff(c_144,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_47,c_46,c_129])).

tff(c_146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_73,c_144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:08:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.14  
% 1.68/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.14  %$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3
% 1.68/1.14  
% 1.68/1.14  %Foreground sorts:
% 1.68/1.14  
% 1.68/1.14  
% 1.68/1.14  %Background operators:
% 1.68/1.14  
% 1.68/1.14  
% 1.68/1.14  %Foreground operators:
% 1.68/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.14  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 1.68/1.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.68/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.14  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.68/1.14  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 1.68/1.14  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.68/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.14  
% 1.83/1.15  tff(f_76, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_xboole_0(A, B) & ~(A = B)) & ~r2_xboole_0(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_ordinal1)).
% 1.83/1.15  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.83/1.15  tff(f_38, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 1.83/1.15  tff(f_60, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 1.83/1.15  tff(f_45, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 1.83/1.15  tff(c_22, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.83/1.15  tff(c_51, plain, (![A_19, B_20]: (r2_xboole_0(A_19, B_20) | B_20=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.83/1.15  tff(c_20, plain, (~r2_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.83/1.15  tff(c_64, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_51, c_20])).
% 1.83/1.15  tff(c_73, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_22, c_64])).
% 1.83/1.15  tff(c_28, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.83/1.15  tff(c_26, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.83/1.15  tff(c_39, plain, (![A_14]: (v1_ordinal1(A_14) | ~v3_ordinal1(A_14))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.83/1.15  tff(c_47, plain, (v1_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_39])).
% 1.83/1.15  tff(c_46, plain, (v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_39])).
% 1.83/1.15  tff(c_95, plain, (![B_23, A_24]: (r2_hidden(B_23, A_24) | B_23=A_24 | r2_hidden(A_24, B_23) | ~v3_ordinal1(B_23) | ~v3_ordinal1(A_24))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.83/1.15  tff(c_12, plain, (![B_7, A_4]: (r1_tarski(B_7, A_4) | ~r2_hidden(B_7, A_4) | ~v1_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.83/1.15  tff(c_104, plain, (![B_25, A_26]: (r1_tarski(B_25, A_26) | ~v1_ordinal1(A_26) | B_25=A_26 | r2_hidden(A_26, B_25) | ~v3_ordinal1(B_25) | ~v3_ordinal1(A_26))), inference(resolution, [status(thm)], [c_95, c_12])).
% 1.83/1.15  tff(c_125, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | ~v1_ordinal1(B_28) | r1_tarski(B_28, A_27) | ~v1_ordinal1(A_27) | B_28=A_27 | ~v3_ordinal1(B_28) | ~v3_ordinal1(A_27))), inference(resolution, [status(thm)], [c_104, c_12])).
% 1.83/1.15  tff(c_24, plain, (~r2_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.83/1.15  tff(c_61, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_51, c_24])).
% 1.83/1.15  tff(c_70, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_22, c_61])).
% 1.83/1.15  tff(c_129, plain, (~v1_ordinal1('#skF_3') | r1_tarski('#skF_3', '#skF_2') | ~v1_ordinal1('#skF_2') | '#skF_2'='#skF_3' | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_125, c_70])).
% 1.83/1.15  tff(c_144, plain, (r1_tarski('#skF_3', '#skF_2') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_47, c_46, c_129])).
% 1.83/1.15  tff(c_146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_73, c_144])).
% 1.83/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.15  
% 1.83/1.15  Inference rules
% 1.83/1.15  ----------------------
% 1.83/1.15  #Ref     : 0
% 1.83/1.15  #Sup     : 16
% 1.83/1.15  #Fact    : 4
% 1.83/1.15  #Define  : 0
% 1.83/1.15  #Split   : 0
% 1.83/1.15  #Chain   : 0
% 1.83/1.15  #Close   : 0
% 1.83/1.15  
% 1.83/1.15  Ordering : KBO
% 1.83/1.15  
% 1.83/1.15  Simplification rules
% 1.83/1.15  ----------------------
% 1.83/1.15  #Subsume      : 1
% 1.83/1.15  #Demod        : 4
% 1.83/1.15  #Tautology    : 7
% 1.83/1.15  #SimpNegUnit  : 3
% 1.83/1.15  #BackRed      : 0
% 1.83/1.15  
% 1.83/1.15  #Partial instantiations: 0
% 1.83/1.15  #Strategies tried      : 1
% 1.83/1.15  
% 1.83/1.15  Timing (in seconds)
% 1.83/1.15  ----------------------
% 1.83/1.15  Preprocessing        : 0.27
% 1.83/1.15  Parsing              : 0.14
% 1.83/1.15  CNF conversion       : 0.02
% 1.83/1.15  Main loop            : 0.13
% 1.83/1.15  Inferencing          : 0.06
% 1.83/1.15  Reduction            : 0.03
% 1.83/1.15  Demodulation         : 0.02
% 1.83/1.15  BG Simplification    : 0.01
% 1.83/1.15  Subsumption          : 0.02
% 1.83/1.15  Abstraction          : 0.01
% 1.83/1.15  MUC search           : 0.00
% 1.83/1.15  Cooper               : 0.00
% 1.83/1.15  Total                : 0.42
% 1.83/1.15  Index Insertion      : 0.00
% 1.83/1.15  Index Deletion       : 0.00
% 1.83/1.15  Index Matching       : 0.00
% 1.83/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
