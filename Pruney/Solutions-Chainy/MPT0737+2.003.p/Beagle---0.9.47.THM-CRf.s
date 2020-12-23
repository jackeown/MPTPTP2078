%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:04 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   40 (  59 expanded)
%              Number of leaves         :   18 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 ( 113 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_33,axiom,(
    ! [A,B] : r3_xboole_0(A,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r3_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        | r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => r3_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_ordinal1)).

tff(f_39,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_61,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_8,plain,(
    ! [A_3] : r3_xboole_0(A_3,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_63,plain,(
    ! [B_25,A_26] :
      ( r1_tarski(B_25,A_26)
      | r1_tarski(A_26,B_25)
      | ~ r3_xboole_0(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_63])).

tff(c_53,plain,(
    ! [B_21,A_22] :
      ( ~ r1_tarski(B_21,A_22)
      | r3_xboole_0(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ~ r3_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_57,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_53,c_22])).

tff(c_26,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    ! [A_15] :
      ( v1_ordinal1(A_15)
      | ~ v3_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    v1_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_28])).

tff(c_35,plain,(
    v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_28])).

tff(c_93,plain,(
    ! [B_28,A_29] :
      ( r2_hidden(B_28,A_29)
      | B_28 = A_29
      | r2_hidden(A_29,B_28)
      | ~ v3_ordinal1(B_28)
      | ~ v3_ordinal1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [B_9,A_6] :
      ( r1_tarski(B_9,A_6)
      | ~ r2_hidden(B_9,A_6)
      | ~ v1_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_102,plain,(
    ! [B_30,A_31] :
      ( r1_tarski(B_30,A_31)
      | ~ v1_ordinal1(A_31)
      | B_30 = A_31
      | r2_hidden(A_31,B_30)
      | ~ v3_ordinal1(B_30)
      | ~ v3_ordinal1(A_31) ) ),
    inference(resolution,[status(thm)],[c_93,c_14])).

tff(c_125,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ v1_ordinal1(B_33)
      | r1_tarski(B_33,A_32)
      | ~ v1_ordinal1(A_32)
      | B_33 = A_32
      | ~ v3_ordinal1(B_33)
      | ~ v3_ordinal1(A_32) ) ),
    inference(resolution,[status(thm)],[c_102,c_14])).

tff(c_48,plain,(
    ! [A_19,B_20] :
      ( ~ r1_tarski(A_19,B_20)
      | r3_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_22])).

tff(c_129,plain,
    ( ~ v1_ordinal1('#skF_3')
    | r1_tarski('#skF_3','#skF_2')
    | ~ v1_ordinal1('#skF_2')
    | '#skF_2' = '#skF_3'
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_125,c_52])).

tff(c_144,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_36,c_35,c_129])).

tff(c_145,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_144])).

tff(c_152,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_57])).

tff(c_160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:09:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.14  
% 1.81/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.14  %$ r3_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3
% 1.81/1.14  
% 1.81/1.14  %Foreground sorts:
% 1.81/1.14  
% 1.81/1.14  
% 1.81/1.14  %Background operators:
% 1.81/1.14  
% 1.81/1.14  
% 1.81/1.14  %Foreground operators:
% 1.81/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.14  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 1.81/1.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.81/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.14  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.81/1.14  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 1.81/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.14  tff(r3_xboole_0, type, r3_xboole_0: ($i * $i) > $o).
% 1.81/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.14  
% 1.81/1.16  tff(f_33, axiom, (![A, B]: r3_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_xboole_0)).
% 1.81/1.16  tff(f_31, axiom, (![A, B]: (r3_xboole_0(A, B) <=> (r1_tarski(A, B) | r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_xboole_0)).
% 1.81/1.16  tff(f_69, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => r3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_ordinal1)).
% 1.81/1.16  tff(f_39, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 1.81/1.16  tff(f_61, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 1.81/1.16  tff(f_46, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 1.81/1.16  tff(c_8, plain, (![A_3]: (r3_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.16  tff(c_63, plain, (![B_25, A_26]: (r1_tarski(B_25, A_26) | r1_tarski(A_26, B_25) | ~r3_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.16  tff(c_75, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_8, c_63])).
% 1.81/1.16  tff(c_53, plain, (![B_21, A_22]: (~r1_tarski(B_21, A_22) | r3_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.16  tff(c_22, plain, (~r3_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.81/1.16  tff(c_57, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_53, c_22])).
% 1.81/1.16  tff(c_26, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.81/1.16  tff(c_24, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.81/1.16  tff(c_28, plain, (![A_15]: (v1_ordinal1(A_15) | ~v3_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.81/1.16  tff(c_36, plain, (v1_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_28])).
% 1.81/1.16  tff(c_35, plain, (v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_28])).
% 1.81/1.16  tff(c_93, plain, (![B_28, A_29]: (r2_hidden(B_28, A_29) | B_28=A_29 | r2_hidden(A_29, B_28) | ~v3_ordinal1(B_28) | ~v3_ordinal1(A_29))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.81/1.16  tff(c_14, plain, (![B_9, A_6]: (r1_tarski(B_9, A_6) | ~r2_hidden(B_9, A_6) | ~v1_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.81/1.16  tff(c_102, plain, (![B_30, A_31]: (r1_tarski(B_30, A_31) | ~v1_ordinal1(A_31) | B_30=A_31 | r2_hidden(A_31, B_30) | ~v3_ordinal1(B_30) | ~v3_ordinal1(A_31))), inference(resolution, [status(thm)], [c_93, c_14])).
% 1.81/1.16  tff(c_125, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~v1_ordinal1(B_33) | r1_tarski(B_33, A_32) | ~v1_ordinal1(A_32) | B_33=A_32 | ~v3_ordinal1(B_33) | ~v3_ordinal1(A_32))), inference(resolution, [status(thm)], [c_102, c_14])).
% 1.81/1.16  tff(c_48, plain, (![A_19, B_20]: (~r1_tarski(A_19, B_20) | r3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.16  tff(c_52, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_22])).
% 1.81/1.16  tff(c_129, plain, (~v1_ordinal1('#skF_3') | r1_tarski('#skF_3', '#skF_2') | ~v1_ordinal1('#skF_2') | '#skF_2'='#skF_3' | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_125, c_52])).
% 1.81/1.16  tff(c_144, plain, (r1_tarski('#skF_3', '#skF_2') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_36, c_35, c_129])).
% 1.81/1.16  tff(c_145, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_57, c_144])).
% 1.81/1.16  tff(c_152, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_57])).
% 1.81/1.16  tff(c_160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_152])).
% 1.81/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.16  
% 1.81/1.16  Inference rules
% 1.81/1.16  ----------------------
% 1.81/1.16  #Ref     : 0
% 1.81/1.16  #Sup     : 17
% 1.81/1.16  #Fact    : 4
% 1.81/1.16  #Define  : 0
% 1.81/1.16  #Split   : 0
% 1.81/1.16  #Chain   : 0
% 1.81/1.16  #Close   : 0
% 1.81/1.16  
% 1.81/1.16  Ordering : KBO
% 1.81/1.16  
% 1.81/1.16  Simplification rules
% 1.81/1.16  ----------------------
% 1.81/1.16  #Subsume      : 3
% 1.81/1.16  #Demod        : 17
% 1.81/1.16  #Tautology    : 7
% 1.81/1.16  #SimpNegUnit  : 2
% 1.81/1.16  #BackRed      : 6
% 1.81/1.16  
% 1.81/1.16  #Partial instantiations: 0
% 1.81/1.16  #Strategies tried      : 1
% 1.81/1.16  
% 1.81/1.16  Timing (in seconds)
% 1.81/1.16  ----------------------
% 1.81/1.16  Preprocessing        : 0.25
% 1.81/1.16  Parsing              : 0.14
% 1.81/1.16  CNF conversion       : 0.02
% 1.81/1.16  Main loop            : 0.15
% 1.81/1.16  Inferencing          : 0.07
% 1.81/1.16  Reduction            : 0.04
% 1.81/1.16  Demodulation         : 0.03
% 1.81/1.16  BG Simplification    : 0.01
% 1.81/1.16  Subsumption          : 0.03
% 1.81/1.16  Abstraction          : 0.01
% 1.81/1.16  MUC search           : 0.00
% 1.81/1.16  Cooper               : 0.00
% 1.81/1.16  Total                : 0.43
% 1.81/1.16  Index Insertion      : 0.00
% 1.81/1.16  Index Deletion       : 0.00
% 1.81/1.16  Index Matching       : 0.00
% 1.81/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
