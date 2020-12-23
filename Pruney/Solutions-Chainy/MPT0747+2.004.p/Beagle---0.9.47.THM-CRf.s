%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:23 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   38 (  55 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   57 ( 100 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v3_ordinal1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A] :
      ( ! [B] :
          ( r2_hidden(B,A)
         => ( v3_ordinal1(B)
            & r1_tarski(B,A) ) )
     => v3_ordinal1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_ordinal1)).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ~ ! [B] :
            ( r2_hidden(B,A)
          <=> v3_ordinal1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

tff(c_25,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_2'(A_16),A_16)
      | v3_ordinal1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [B_13] :
      ( v3_ordinal1(B_13)
      | ~ r2_hidden(B_13,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,
    ( v3_ordinal1('#skF_2'('#skF_3'))
    | v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_25,c_16])).

tff(c_31,plain,(
    v3_ordinal1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_61,plain,(
    ! [A_26,B_27] :
      ( r2_hidden('#skF_1'(A_26,B_27),A_26)
      | r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [A_28] : r1_tarski(A_28,A_28) ),
    inference(resolution,[status(thm)],[c_61,c_4])).

tff(c_18,plain,(
    ! [B_13] :
      ( r2_hidden(B_13,'#skF_3')
      | ~ v3_ordinal1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ! [B_17,A_18] :
      ( ~ r1_tarski(B_17,A_18)
      | ~ r2_hidden(A_18,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_40,plain,(
    ! [B_13] :
      ( ~ r1_tarski('#skF_3',B_13)
      | ~ v3_ordinal1(B_13) ) ),
    inference(resolution,[status(thm)],[c_18,c_32])).

tff(c_84,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_40])).

tff(c_88,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_84])).

tff(c_90,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_89,plain,(
    v3_ordinal1('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_118,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_1'(A_38,B_39),A_38)
      | r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v3_ordinal1(A_6)
      | ~ r2_hidden(A_6,B_7)
      | ~ v3_ordinal1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_213,plain,(
    ! [A_57,B_58] :
      ( v3_ordinal1('#skF_1'(A_57,B_58))
      | ~ v3_ordinal1(A_57)
      | r1_tarski(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_118,c_8])).

tff(c_111,plain,(
    ! [A_35,B_36] :
      ( ~ r2_hidden('#skF_1'(A_35,B_36),B_36)
      | r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_116,plain,(
    ! [A_35] :
      ( r1_tarski(A_35,'#skF_3')
      | ~ v3_ordinal1('#skF_1'(A_35,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_18,c_111])).

tff(c_223,plain,(
    ! [A_59] :
      ( ~ v3_ordinal1(A_59)
      | r1_tarski(A_59,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_213,c_116])).

tff(c_10,plain,(
    ! [A_8] :
      ( ~ r1_tarski('#skF_2'(A_8),A_8)
      | ~ v3_ordinal1('#skF_2'(A_8))
      | v3_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_229,plain,
    ( v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2'('#skF_3')) ),
    inference(resolution,[status(thm)],[c_223,c_10])).

tff(c_237,plain,(
    v3_ordinal1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_229])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:04:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.27  
% 2.03/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.28  %$ r2_hidden > r1_tarski > v3_ordinal1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.03/1.28  
% 2.03/1.28  %Foreground sorts:
% 2.03/1.28  
% 2.03/1.28  
% 2.03/1.28  %Background operators:
% 2.03/1.28  
% 2.03/1.28  
% 2.03/1.28  %Foreground operators:
% 2.03/1.28  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.03/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.28  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.03/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.03/1.28  
% 2.03/1.29  tff(f_47, axiom, (![A]: ((![B]: (r2_hidden(B, A) => (v3_ordinal1(B) & r1_tarski(B, A)))) => v3_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_ordinal1)).
% 2.03/1.29  tff(f_59, negated_conjecture, ~(![A]: ~(![B]: (r2_hidden(B, A) <=> v3_ordinal1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_ordinal1)).
% 2.03/1.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.03/1.29  tff(f_52, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.03/1.29  tff(f_38, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 2.03/1.29  tff(c_25, plain, (![A_16]: (r2_hidden('#skF_2'(A_16), A_16) | v3_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.03/1.29  tff(c_16, plain, (![B_13]: (v3_ordinal1(B_13) | ~r2_hidden(B_13, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.03/1.29  tff(c_30, plain, (v3_ordinal1('#skF_2'('#skF_3')) | v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_25, c_16])).
% 2.03/1.29  tff(c_31, plain, (v3_ordinal1('#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 2.03/1.29  tff(c_61, plain, (![A_26, B_27]: (r2_hidden('#skF_1'(A_26, B_27), A_26) | r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.03/1.29  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.03/1.29  tff(c_80, plain, (![A_28]: (r1_tarski(A_28, A_28))), inference(resolution, [status(thm)], [c_61, c_4])).
% 2.03/1.29  tff(c_18, plain, (![B_13]: (r2_hidden(B_13, '#skF_3') | ~v3_ordinal1(B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.03/1.29  tff(c_32, plain, (![B_17, A_18]: (~r1_tarski(B_17, A_18) | ~r2_hidden(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.03/1.29  tff(c_40, plain, (![B_13]: (~r1_tarski('#skF_3', B_13) | ~v3_ordinal1(B_13))), inference(resolution, [status(thm)], [c_18, c_32])).
% 2.03/1.29  tff(c_84, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_40])).
% 2.03/1.29  tff(c_88, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31, c_84])).
% 2.03/1.29  tff(c_90, plain, (~v3_ordinal1('#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.03/1.29  tff(c_89, plain, (v3_ordinal1('#skF_2'('#skF_3'))), inference(splitRight, [status(thm)], [c_30])).
% 2.03/1.29  tff(c_118, plain, (![A_38, B_39]: (r2_hidden('#skF_1'(A_38, B_39), A_38) | r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.03/1.29  tff(c_8, plain, (![A_6, B_7]: (v3_ordinal1(A_6) | ~r2_hidden(A_6, B_7) | ~v3_ordinal1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.03/1.29  tff(c_213, plain, (![A_57, B_58]: (v3_ordinal1('#skF_1'(A_57, B_58)) | ~v3_ordinal1(A_57) | r1_tarski(A_57, B_58))), inference(resolution, [status(thm)], [c_118, c_8])).
% 2.03/1.29  tff(c_111, plain, (![A_35, B_36]: (~r2_hidden('#skF_1'(A_35, B_36), B_36) | r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.03/1.29  tff(c_116, plain, (![A_35]: (r1_tarski(A_35, '#skF_3') | ~v3_ordinal1('#skF_1'(A_35, '#skF_3')))), inference(resolution, [status(thm)], [c_18, c_111])).
% 2.03/1.29  tff(c_223, plain, (![A_59]: (~v3_ordinal1(A_59) | r1_tarski(A_59, '#skF_3'))), inference(resolution, [status(thm)], [c_213, c_116])).
% 2.03/1.29  tff(c_10, plain, (![A_8]: (~r1_tarski('#skF_2'(A_8), A_8) | ~v3_ordinal1('#skF_2'(A_8)) | v3_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.03/1.29  tff(c_229, plain, (v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2'('#skF_3'))), inference(resolution, [status(thm)], [c_223, c_10])).
% 2.03/1.29  tff(c_237, plain, (v3_ordinal1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_229])).
% 2.03/1.29  tff(c_239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_237])).
% 2.03/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.29  
% 2.03/1.29  Inference rules
% 2.03/1.29  ----------------------
% 2.03/1.29  #Ref     : 0
% 2.03/1.29  #Sup     : 42
% 2.03/1.29  #Fact    : 0
% 2.03/1.29  #Define  : 0
% 2.03/1.29  #Split   : 1
% 2.03/1.29  #Chain   : 0
% 2.03/1.29  #Close   : 0
% 2.03/1.29  
% 2.03/1.29  Ordering : KBO
% 2.03/1.29  
% 2.03/1.29  Simplification rules
% 2.03/1.29  ----------------------
% 2.03/1.29  #Subsume      : 5
% 2.03/1.29  #Demod        : 5
% 2.03/1.29  #Tautology    : 7
% 2.03/1.29  #SimpNegUnit  : 1
% 2.03/1.29  #BackRed      : 0
% 2.03/1.29  
% 2.03/1.29  #Partial instantiations: 0
% 2.03/1.29  #Strategies tried      : 1
% 2.03/1.29  
% 2.03/1.29  Timing (in seconds)
% 2.03/1.29  ----------------------
% 2.03/1.29  Preprocessing        : 0.27
% 2.03/1.29  Parsing              : 0.15
% 2.03/1.29  CNF conversion       : 0.02
% 2.03/1.29  Main loop            : 0.20
% 2.03/1.29  Inferencing          : 0.09
% 2.03/1.29  Reduction            : 0.04
% 2.03/1.29  Demodulation         : 0.03
% 2.03/1.29  BG Simplification    : 0.01
% 2.03/1.29  Subsumption          : 0.04
% 2.03/1.29  Abstraction          : 0.01
% 2.03/1.29  MUC search           : 0.00
% 2.03/1.29  Cooper               : 0.00
% 2.03/1.29  Total                : 0.50
% 2.03/1.29  Index Insertion      : 0.00
% 2.03/1.29  Index Deletion       : 0.00
% 2.03/1.29  Index Matching       : 0.00
% 2.03/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
