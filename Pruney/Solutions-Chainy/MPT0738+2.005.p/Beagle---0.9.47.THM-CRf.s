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
% DateTime   : Thu Dec  3 10:06:04 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   36 (  63 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :   61 ( 142 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r1_ordinal1(A,B)
              | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_56,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_61,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_14,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_ordinal1(B_2,A_1)
      | r1_ordinal1(A_1,B_2)
      | ~ v3_ordinal1(B_2)
      | ~ v3_ordinal1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_ordinal1(A_3,B_4)
      | ~ v3_ordinal1(B_4)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,(
    ! [B_2] :
      ( ~ v3_ordinal1(B_2)
      | r1_ordinal1(B_2,B_2) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2])).

tff(c_60,plain,(
    ! [B_20,A_21] :
      ( r2_hidden(B_20,A_21)
      | B_20 = A_21
      | r2_hidden(A_21,B_20)
      | ~ v3_ordinal1(B_20)
      | ~ v3_ordinal1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_72,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_12])).

tff(c_80,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_72])).

tff(c_81,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_82,plain,(
    ~ r1_ordinal1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_14])).

tff(c_92,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_82])).

tff(c_98,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_92])).

tff(c_99,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( ~ r1_tarski(B_9,A_8)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_104,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_99,c_10])).

tff(c_107,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_110,plain,(
    ~ r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_107])).

tff(c_113,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_110])).

tff(c_119,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_113])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:50:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.14  
% 1.61/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.14  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > #skF_2 > #skF_1
% 1.61/1.14  
% 1.61/1.14  %Foreground sorts:
% 1.61/1.14  
% 1.61/1.14  
% 1.61/1.14  %Background operators:
% 1.61/1.14  
% 1.61/1.14  
% 1.61/1.14  %Foreground operators:
% 1.61/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.14  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 1.61/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.14  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.61/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.14  
% 1.75/1.15  tff(f_71, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 1.75/1.15  tff(f_33, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 1.75/1.15  tff(f_41, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 1.75/1.15  tff(f_56, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 1.75/1.15  tff(f_61, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.75/1.15  tff(c_14, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.75/1.15  tff(c_18, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.75/1.15  tff(c_16, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.75/1.15  tff(c_2, plain, (![B_2, A_1]: (r1_ordinal1(B_2, A_1) | r1_ordinal1(A_1, B_2) | ~v3_ordinal1(B_2) | ~v3_ordinal1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.75/1.15  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~r1_ordinal1(A_3, B_4) | ~v3_ordinal1(B_4) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.75/1.15  tff(c_38, plain, (![B_2]: (~v3_ordinal1(B_2) | r1_ordinal1(B_2, B_2))), inference(factorization, [status(thm), theory('equality')], [c_2])).
% 1.75/1.15  tff(c_60, plain, (![B_20, A_21]: (r2_hidden(B_20, A_21) | B_20=A_21 | r2_hidden(A_21, B_20) | ~v3_ordinal1(B_20) | ~v3_ordinal1(A_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.75/1.15  tff(c_12, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.75/1.15  tff(c_72, plain, (r2_hidden('#skF_1', '#skF_2') | '#skF_2'='#skF_1' | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_60, c_12])).
% 1.75/1.15  tff(c_80, plain, (r2_hidden('#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_72])).
% 1.75/1.15  tff(c_81, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_80])).
% 1.75/1.15  tff(c_82, plain, (~r1_ordinal1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_14])).
% 1.75/1.15  tff(c_92, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_38, c_82])).
% 1.75/1.15  tff(c_98, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_92])).
% 1.75/1.15  tff(c_99, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_80])).
% 1.75/1.15  tff(c_10, plain, (![B_9, A_8]: (~r1_tarski(B_9, A_8) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.75/1.15  tff(c_104, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_99, c_10])).
% 1.75/1.15  tff(c_107, plain, (~r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_6, c_104])).
% 1.75/1.15  tff(c_110, plain, (~r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_107])).
% 1.75/1.15  tff(c_113, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_2, c_110])).
% 1.75/1.15  tff(c_119, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_113])).
% 1.75/1.15  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_119])).
% 1.75/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.15  
% 1.75/1.15  Inference rules
% 1.75/1.15  ----------------------
% 1.75/1.15  #Ref     : 0
% 1.75/1.15  #Sup     : 12
% 1.75/1.15  #Fact    : 4
% 1.75/1.15  #Define  : 0
% 1.75/1.15  #Split   : 1
% 1.75/1.15  #Chain   : 0
% 1.75/1.15  #Close   : 0
% 1.75/1.15  
% 1.75/1.15  Ordering : KBO
% 1.75/1.15  
% 1.75/1.15  Simplification rules
% 1.75/1.15  ----------------------
% 1.75/1.15  #Subsume      : 1
% 1.75/1.15  #Demod        : 13
% 1.75/1.15  #Tautology    : 6
% 1.75/1.15  #SimpNegUnit  : 1
% 1.75/1.15  #BackRed      : 3
% 1.75/1.15  
% 1.75/1.15  #Partial instantiations: 0
% 1.75/1.15  #Strategies tried      : 1
% 1.75/1.15  
% 1.75/1.15  Timing (in seconds)
% 1.75/1.15  ----------------------
% 1.75/1.16  Preprocessing        : 0.25
% 1.75/1.16  Parsing              : 0.14
% 1.75/1.16  CNF conversion       : 0.02
% 1.75/1.16  Main loop            : 0.13
% 1.75/1.16  Inferencing          : 0.06
% 1.75/1.16  Reduction            : 0.03
% 1.75/1.16  Demodulation         : 0.02
% 1.75/1.16  BG Simplification    : 0.01
% 1.75/1.16  Subsumption          : 0.02
% 1.75/1.16  Abstraction          : 0.00
% 1.75/1.16  MUC search           : 0.00
% 1.75/1.16  Cooper               : 0.00
% 1.75/1.16  Total                : 0.41
% 1.75/1.16  Index Insertion      : 0.00
% 1.75/1.16  Index Deletion       : 0.00
% 1.75/1.16  Index Matching       : 0.00
% 1.75/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
