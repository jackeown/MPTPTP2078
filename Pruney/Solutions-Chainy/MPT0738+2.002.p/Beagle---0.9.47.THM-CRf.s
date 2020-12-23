%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:04 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   42 (  75 expanded)
%              Number of leaves         :   18 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 ( 167 expanded)
%              Number of equality atoms :    6 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r1_ordinal1(A,B)
              | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_54,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

tff(c_26,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( r1_ordinal1(B_5,A_4)
      | r1_ordinal1(A_4,B_5)
      | ~ v3_ordinal1(B_5)
      | ~ v3_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_70,plain,(
    ! [B_5] :
      ( ~ v3_ordinal1(B_5)
      | r1_ordinal1(B_5,B_5) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_12])).

tff(c_22,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ r1_ordinal1(A_6,B_7)
      | ~ v3_ordinal1(B_7)
      | ~ v3_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    ! [A_13] :
      ( v1_ordinal1(A_13)
      | ~ v3_ordinal1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_35,plain,(
    v1_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_28])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_22,B_23] :
      ( r2_hidden(A_22,B_23)
      | ~ r2_xboole_0(A_22,B_23)
      | ~ v3_ordinal1(B_23)
      | ~ v1_ordinal1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_87,plain,(
    ! [A_28,B_29] :
      ( r2_hidden(A_28,B_29)
      | ~ v3_ordinal1(B_29)
      | ~ v1_ordinal1(A_28)
      | B_29 = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_2,c_76])).

tff(c_20,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_90,plain,
    ( ~ v3_ordinal1('#skF_1')
    | ~ v1_ordinal1('#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_87,c_20])).

tff(c_93,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_26,c_90])).

tff(c_94,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_97,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_94])).

tff(c_100,plain,(
    ~ r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_97])).

tff(c_103,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_100])).

tff(c_109,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_103])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_109])).

tff(c_112,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_116,plain,(
    ~ r1_ordinal1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_22])).

tff(c_142,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_116])).

tff(c_148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.19  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_2 > #skF_1
% 1.88/1.19  
% 1.88/1.19  %Foreground sorts:
% 1.88/1.19  
% 1.88/1.19  
% 1.88/1.19  %Background operators:
% 1.88/1.19  
% 1.88/1.19  
% 1.88/1.19  %Foreground operators:
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.19  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 1.88/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.19  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 1.88/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.19  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.88/1.19  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 1.88/1.19  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.19  
% 1.96/1.20  tff(f_73, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 1.96/1.20  tff(f_46, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 1.96/1.20  tff(f_54, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 1.96/1.20  tff(f_38, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 1.96/1.20  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.96/1.20  tff(f_63, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_ordinal1)).
% 1.96/1.20  tff(c_26, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.96/1.20  tff(c_12, plain, (![B_5, A_4]: (r1_ordinal1(B_5, A_4) | r1_ordinal1(A_4, B_5) | ~v3_ordinal1(B_5) | ~v3_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.96/1.20  tff(c_70, plain, (![B_5]: (~v3_ordinal1(B_5) | r1_ordinal1(B_5, B_5))), inference(factorization, [status(thm), theory('equality')], [c_12])).
% 1.96/1.20  tff(c_22, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.96/1.20  tff(c_24, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.96/1.20  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~r1_ordinal1(A_6, B_7) | ~v3_ordinal1(B_7) | ~v3_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.96/1.20  tff(c_28, plain, (![A_13]: (v1_ordinal1(A_13) | ~v3_ordinal1(A_13))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.96/1.20  tff(c_35, plain, (v1_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_28])).
% 1.96/1.20  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.20  tff(c_76, plain, (![A_22, B_23]: (r2_hidden(A_22, B_23) | ~r2_xboole_0(A_22, B_23) | ~v3_ordinal1(B_23) | ~v1_ordinal1(A_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.96/1.20  tff(c_87, plain, (![A_28, B_29]: (r2_hidden(A_28, B_29) | ~v3_ordinal1(B_29) | ~v1_ordinal1(A_28) | B_29=A_28 | ~r1_tarski(A_28, B_29))), inference(resolution, [status(thm)], [c_2, c_76])).
% 1.96/1.20  tff(c_20, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.96/1.20  tff(c_90, plain, (~v3_ordinal1('#skF_1') | ~v1_ordinal1('#skF_2') | '#skF_2'='#skF_1' | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_87, c_20])).
% 1.96/1.20  tff(c_93, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_26, c_90])).
% 1.96/1.20  tff(c_94, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_93])).
% 1.96/1.20  tff(c_97, plain, (~r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_94])).
% 1.96/1.20  tff(c_100, plain, (~r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_97])).
% 1.96/1.20  tff(c_103, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_12, c_100])).
% 1.96/1.20  tff(c_109, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_103])).
% 1.96/1.20  tff(c_111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_109])).
% 1.96/1.20  tff(c_112, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_93])).
% 1.96/1.20  tff(c_116, plain, (~r1_ordinal1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_22])).
% 1.96/1.20  tff(c_142, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_70, c_116])).
% 1.96/1.20  tff(c_148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_142])).
% 1.96/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.20  
% 1.96/1.20  Inference rules
% 1.96/1.20  ----------------------
% 1.96/1.20  #Ref     : 0
% 1.96/1.20  #Sup     : 17
% 1.96/1.20  #Fact    : 2
% 1.96/1.20  #Define  : 0
% 1.96/1.20  #Split   : 1
% 1.96/1.20  #Chain   : 0
% 1.96/1.20  #Close   : 0
% 1.96/1.20  
% 1.96/1.20  Ordering : KBO
% 1.96/1.20  
% 1.96/1.20  Simplification rules
% 1.96/1.20  ----------------------
% 1.96/1.20  #Subsume      : 1
% 1.96/1.20  #Demod        : 20
% 1.96/1.20  #Tautology    : 9
% 1.96/1.20  #SimpNegUnit  : 1
% 1.96/1.20  #BackRed      : 5
% 1.96/1.20  
% 1.96/1.20  #Partial instantiations: 0
% 1.96/1.20  #Strategies tried      : 1
% 1.96/1.20  
% 1.96/1.20  Timing (in seconds)
% 1.96/1.20  ----------------------
% 1.96/1.20  Preprocessing        : 0.28
% 1.96/1.20  Parsing              : 0.15
% 1.96/1.20  CNF conversion       : 0.02
% 1.96/1.20  Main loop            : 0.16
% 1.96/1.20  Inferencing          : 0.07
% 1.96/1.20  Reduction            : 0.04
% 1.96/1.20  Demodulation         : 0.03
% 1.96/1.20  BG Simplification    : 0.01
% 1.96/1.20  Subsumption          : 0.02
% 1.96/1.20  Abstraction          : 0.01
% 1.96/1.20  MUC search           : 0.00
% 1.96/1.21  Cooper               : 0.00
% 1.96/1.21  Total                : 0.47
% 1.96/1.21  Index Insertion      : 0.00
% 1.96/1.21  Index Deletion       : 0.00
% 1.96/1.21  Index Matching       : 0.00
% 1.96/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
