%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:31 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   40 (  54 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   65 ( 115 expanded)
%              Number of equality atoms :    6 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ~ ( ~ r2_xboole_0(A,B)
                & A != B
                & ~ r2_xboole_0(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_45,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
    <=> ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_ordinal1)).

tff(f_62,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_34,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_99,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | ~ r1_ordinal1(A_28,B_29)
      | ~ v3_ordinal1(B_29)
      | ~ v3_ordinal1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_71,plain,(
    ! [A_24,B_25] :
      ( r2_xboole_0(A_24,B_25)
      | B_25 = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ~ r2_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_77,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_30])).

tff(c_88,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_77])).

tff(c_105,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_99,c_88])).

tff(c_115,plain,(
    ~ r1_ordinal1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_105])).

tff(c_45,plain,(
    ! [A_16] :
      ( v1_ordinal1(A_16)
      | ~ v3_ordinal1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_53,plain,(
    v1_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_45])).

tff(c_94,plain,(
    ! [B_26,A_27] :
      ( r2_hidden(B_26,A_27)
      | r1_ordinal1(A_27,B_26)
      | ~ v3_ordinal1(B_26)
      | ~ v3_ordinal1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [B_6,A_3] :
      ( r1_tarski(B_6,A_3)
      | ~ r2_hidden(B_6,A_3)
      | ~ v1_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_122,plain,(
    ! [B_32,A_33] :
      ( r1_tarski(B_32,A_33)
      | ~ v1_ordinal1(A_33)
      | r1_ordinal1(A_33,B_32)
      | ~ v3_ordinal1(B_32)
      | ~ v3_ordinal1(A_33) ) ),
    inference(resolution,[status(thm)],[c_94,c_8])).

tff(c_26,plain,(
    ~ r2_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_80,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_71,c_26])).

tff(c_91,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_80])).

tff(c_128,plain,
    ( ~ v1_ordinal1('#skF_2')
    | r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_122,c_91])).

tff(c_139,plain,(
    r1_ordinal1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_53,c_128])).

tff(c_141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 10:56:56 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.19  
% 1.84/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.19  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3
% 1.84/1.19  
% 1.84/1.19  %Foreground sorts:
% 1.84/1.19  
% 1.84/1.19  
% 1.84/1.19  %Background operators:
% 1.84/1.19  
% 1.84/1.19  
% 1.84/1.19  %Foreground operators:
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.19  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 1.84/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.84/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.19  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 1.84/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.19  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.84/1.19  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 1.84/1.19  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.19  
% 1.84/1.20  tff(f_78, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_xboole_0(A, B) & ~(A = B)) & ~r2_xboole_0(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_ordinal1)).
% 1.84/1.20  tff(f_53, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 1.84/1.20  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.84/1.20  tff(f_45, axiom, (![A]: (v3_ordinal1(A) <=> (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_ordinal1)).
% 1.84/1.20  tff(f_62, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 1.84/1.20  tff(f_39, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 1.84/1.20  tff(c_34, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.84/1.20  tff(c_32, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.84/1.20  tff(c_99, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | ~r1_ordinal1(A_28, B_29) | ~v3_ordinal1(B_29) | ~v3_ordinal1(A_28))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.84/1.20  tff(c_28, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.84/1.20  tff(c_71, plain, (![A_24, B_25]: (r2_xboole_0(A_24, B_25) | B_25=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.84/1.20  tff(c_30, plain, (~r2_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.84/1.20  tff(c_77, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_71, c_30])).
% 1.84/1.20  tff(c_88, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_77])).
% 1.84/1.20  tff(c_105, plain, (~r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_99, c_88])).
% 1.84/1.20  tff(c_115, plain, (~r1_ordinal1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_105])).
% 1.84/1.20  tff(c_45, plain, (![A_16]: (v1_ordinal1(A_16) | ~v3_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.84/1.20  tff(c_53, plain, (v1_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_45])).
% 1.84/1.20  tff(c_94, plain, (![B_26, A_27]: (r2_hidden(B_26, A_27) | r1_ordinal1(A_27, B_26) | ~v3_ordinal1(B_26) | ~v3_ordinal1(A_27))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.84/1.20  tff(c_8, plain, (![B_6, A_3]: (r1_tarski(B_6, A_3) | ~r2_hidden(B_6, A_3) | ~v1_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.84/1.20  tff(c_122, plain, (![B_32, A_33]: (r1_tarski(B_32, A_33) | ~v1_ordinal1(A_33) | r1_ordinal1(A_33, B_32) | ~v3_ordinal1(B_32) | ~v3_ordinal1(A_33))), inference(resolution, [status(thm)], [c_94, c_8])).
% 1.84/1.20  tff(c_26, plain, (~r2_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.84/1.20  tff(c_80, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_71, c_26])).
% 1.84/1.20  tff(c_91, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_28, c_80])).
% 1.84/1.20  tff(c_128, plain, (~v1_ordinal1('#skF_2') | r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_122, c_91])).
% 1.84/1.20  tff(c_139, plain, (r1_ordinal1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_53, c_128])).
% 1.84/1.20  tff(c_141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_139])).
% 1.84/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.20  
% 1.84/1.20  Inference rules
% 1.84/1.20  ----------------------
% 1.84/1.20  #Ref     : 0
% 1.84/1.20  #Sup     : 20
% 1.84/1.20  #Fact    : 0
% 1.84/1.20  #Define  : 0
% 1.84/1.20  #Split   : 0
% 1.84/1.20  #Chain   : 0
% 1.84/1.20  #Close   : 0
% 1.84/1.20  
% 1.84/1.20  Ordering : KBO
% 1.84/1.20  
% 1.84/1.20  Simplification rules
% 1.84/1.20  ----------------------
% 1.84/1.20  #Subsume      : 1
% 1.84/1.20  #Demod        : 7
% 1.84/1.20  #Tautology    : 6
% 1.84/1.20  #SimpNegUnit  : 3
% 1.84/1.20  #BackRed      : 0
% 1.84/1.20  
% 1.84/1.20  #Partial instantiations: 0
% 1.84/1.20  #Strategies tried      : 1
% 1.84/1.20  
% 1.84/1.20  Timing (in seconds)
% 1.84/1.20  ----------------------
% 1.84/1.20  Preprocessing        : 0.29
% 1.84/1.20  Parsing              : 0.15
% 1.84/1.20  CNF conversion       : 0.02
% 1.84/1.20  Main loop            : 0.14
% 1.84/1.20  Inferencing          : 0.06
% 1.84/1.21  Reduction            : 0.04
% 1.84/1.21  Demodulation         : 0.02
% 1.84/1.21  BG Simplification    : 0.01
% 1.84/1.21  Subsumption          : 0.02
% 1.84/1.21  Abstraction          : 0.01
% 1.84/1.21  MUC search           : 0.00
% 1.84/1.21  Cooper               : 0.00
% 1.84/1.21  Total                : 0.45
% 1.84/1.21  Index Insertion      : 0.00
% 1.84/1.21  Index Deletion       : 0.00
% 1.84/1.21  Index Matching       : 0.00
% 1.84/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
