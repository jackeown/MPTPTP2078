%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:32 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   29 (  37 expanded)
%              Number of leaves         :   13 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  75 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r1_tarski > v3_ordinal1 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_61,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => r3_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r3_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        | r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

tff(c_18,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_30,plain,(
    ! [A_18,B_19] :
      ( r2_xboole_0(A_18,B_19)
      | B_19 = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ~ r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_20])).

tff(c_47,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_36])).

tff(c_24,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_5,B_7] :
      ( r3_xboole_0(A_5,B_7)
      | ~ v3_ordinal1(B_7)
      | ~ v3_ordinal1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_53,plain,(
    ! [B_20,A_21] :
      ( r1_tarski(B_20,A_21)
      | r1_tarski(A_21,B_20)
      | ~ r3_xboole_0(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_80,plain,(
    ! [B_22,A_23] :
      ( r1_tarski(B_22,A_23)
      | r1_tarski(A_23,B_22)
      | ~ v3_ordinal1(B_22)
      | ~ v3_ordinal1(A_23) ) ),
    inference(resolution,[status(thm)],[c_14,c_53])).

tff(c_16,plain,(
    ~ r2_xboole_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_39,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_16])).

tff(c_50,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_39])).

tff(c_83,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_50])).

tff(c_91,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_83])).

tff(c_93,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_91])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.12  
% 1.60/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.13  %$ r3_xboole_0 > r2_xboole_0 > r1_tarski > v3_ordinal1 > #nlpp > #skF_2 > #skF_1
% 1.60/1.13  
% 1.60/1.13  %Foreground sorts:
% 1.60/1.13  
% 1.60/1.13  
% 1.60/1.13  %Background operators:
% 1.60/1.13  
% 1.60/1.13  
% 1.60/1.13  %Foreground operators:
% 1.60/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.13  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.60/1.13  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.60/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.13  tff(r3_xboole_0, type, r3_xboole_0: ($i * $i) > $o).
% 1.60/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.13  
% 1.60/1.14  tff(f_61, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_xboole_0(A, B) & ~(A = B)) & ~r2_xboole_0(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_ordinal1)).
% 1.60/1.14  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.60/1.14  tff(f_45, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => r3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_ordinal1)).
% 1.60/1.14  tff(f_38, axiom, (![A, B]: (r3_xboole_0(A, B) <=> (r1_tarski(A, B) | r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_xboole_0)).
% 1.60/1.14  tff(c_18, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.60/1.14  tff(c_30, plain, (![A_18, B_19]: (r2_xboole_0(A_18, B_19) | B_19=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.14  tff(c_20, plain, (~r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.60/1.14  tff(c_36, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_20])).
% 1.60/1.14  tff(c_47, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_18, c_36])).
% 1.60/1.14  tff(c_24, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.60/1.14  tff(c_22, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.60/1.14  tff(c_14, plain, (![A_5, B_7]: (r3_xboole_0(A_5, B_7) | ~v3_ordinal1(B_7) | ~v3_ordinal1(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.60/1.14  tff(c_53, plain, (![B_20, A_21]: (r1_tarski(B_20, A_21) | r1_tarski(A_21, B_20) | ~r3_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.60/1.14  tff(c_80, plain, (![B_22, A_23]: (r1_tarski(B_22, A_23) | r1_tarski(A_23, B_22) | ~v3_ordinal1(B_22) | ~v3_ordinal1(A_23))), inference(resolution, [status(thm)], [c_14, c_53])).
% 1.60/1.14  tff(c_16, plain, (~r2_xboole_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.60/1.14  tff(c_39, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_16])).
% 1.60/1.14  tff(c_50, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_18, c_39])).
% 1.60/1.14  tff(c_83, plain, (r1_tarski('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_80, c_50])).
% 1.60/1.14  tff(c_91, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_83])).
% 1.60/1.14  tff(c_93, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_91])).
% 1.60/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.14  
% 1.60/1.14  Inference rules
% 1.60/1.14  ----------------------
% 1.60/1.14  #Ref     : 0
% 1.60/1.14  #Sup     : 9
% 1.60/1.14  #Fact    : 2
% 1.60/1.14  #Define  : 0
% 1.60/1.14  #Split   : 0
% 1.60/1.14  #Chain   : 0
% 1.60/1.14  #Close   : 0
% 1.60/1.14  
% 1.60/1.14  Ordering : KBO
% 1.60/1.14  
% 1.60/1.14  Simplification rules
% 1.60/1.14  ----------------------
% 1.60/1.14  #Subsume      : 0
% 1.60/1.14  #Demod        : 2
% 1.60/1.14  #Tautology    : 4
% 1.60/1.14  #SimpNegUnit  : 3
% 1.60/1.14  #BackRed      : 0
% 1.60/1.14  
% 1.60/1.14  #Partial instantiations: 0
% 1.60/1.14  #Strategies tried      : 1
% 1.60/1.14  
% 1.60/1.14  Timing (in seconds)
% 1.60/1.14  ----------------------
% 1.73/1.14  Preprocessing        : 0.27
% 1.73/1.14  Parsing              : 0.15
% 1.73/1.14  CNF conversion       : 0.02
% 1.73/1.14  Main loop            : 0.10
% 1.73/1.14  Inferencing          : 0.04
% 1.73/1.14  Reduction            : 0.03
% 1.73/1.14  Demodulation         : 0.01
% 1.73/1.14  BG Simplification    : 0.01
% 1.73/1.14  Subsumption          : 0.02
% 1.73/1.14  Abstraction          : 0.00
% 1.73/1.14  MUC search           : 0.00
% 1.73/1.14  Cooper               : 0.00
% 1.73/1.14  Total                : 0.39
% 1.73/1.14  Index Insertion      : 0.00
% 1.73/1.14  Index Deletion       : 0.00
% 1.73/1.14  Index Matching       : 0.00
% 1.73/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
