%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:23 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   32 (  59 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 ( 104 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v3_ordinal1 > #nlpp > #skF_2 > #skF_1 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(f_37,axiom,(
    ! [A] :
      ~ ( ! [B] :
            ( r2_hidden(B,A)
           => v3_ordinal1(B) )
        & ! [B] :
            ( v3_ordinal1(B)
           => ~ r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_ordinal1)).

tff(f_49,negated_conjecture,(
    ~ ! [A] :
        ~ ! [B] :
            ( r2_hidden(B,A)
          <=> v3_ordinal1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_ordinal1)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_28,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(A_14),A_14)
      | v3_ordinal1('#skF_2'(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [B_7] :
      ( v3_ordinal1(B_7)
      | ~ r2_hidden(B_7,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_37,plain,
    ( v3_ordinal1('#skF_1'('#skF_3'))
    | v3_ordinal1('#skF_2'('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_12])).

tff(c_38,plain,(
    v3_ordinal1('#skF_2'('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_37])).

tff(c_39,plain,(
    ! [A_15] :
      ( ~ v3_ordinal1('#skF_1'(A_15))
      | r1_tarski(A_15,'#skF_2'(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [B_7] :
      ( r2_hidden(B_7,'#skF_3')
      | ~ v3_ordinal1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [B_11,A_12] :
      ( ~ r1_tarski(B_11,A_12)
      | ~ r2_hidden(A_12,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_26,plain,(
    ! [B_7] :
      ( ~ r1_tarski('#skF_3',B_7)
      | ~ v3_ordinal1(B_7) ) ),
    inference(resolution,[status(thm)],[c_14,c_22])).

tff(c_43,plain,
    ( ~ v3_ordinal1('#skF_2'('#skF_3'))
    | ~ v3_ordinal1('#skF_1'('#skF_3')) ),
    inference(resolution,[status(thm)],[c_39,c_26])).

tff(c_46,plain,(
    ~ v3_ordinal1('#skF_1'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_43])).

tff(c_48,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_1'(A_17),A_17)
      | r1_tarski(A_17,'#skF_2'(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_55,plain,
    ( v3_ordinal1('#skF_1'('#skF_3'))
    | r1_tarski('#skF_3','#skF_2'('#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_12])).

tff(c_59,plain,(
    r1_tarski('#skF_3','#skF_2'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_55])).

tff(c_62,plain,(
    ~ v3_ordinal1('#skF_2'('#skF_3')) ),
    inference(resolution,[status(thm)],[c_59,c_26])).

tff(c_66,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_62])).

tff(c_67,plain,(
    v3_ordinal1('#skF_1'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_37])).

tff(c_6,plain,(
    ! [A_1] :
      ( ~ v3_ordinal1('#skF_1'(A_1))
      | v3_ordinal1('#skF_2'(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    ~ v3_ordinal1('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_37])).

tff(c_71,plain,(
    ~ v3_ordinal1('#skF_1'('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_68])).

tff(c_75,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.12  
% 1.71/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.13  %$ r2_hidden > r1_tarski > v3_ordinal1 > #nlpp > #skF_2 > #skF_1 > #skF_3
% 1.71/1.13  
% 1.71/1.13  %Foreground sorts:
% 1.71/1.13  
% 1.71/1.13  
% 1.71/1.13  %Background operators:
% 1.71/1.13  
% 1.71/1.13  
% 1.71/1.13  %Foreground operators:
% 1.71/1.13  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.71/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.13  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.13  
% 1.71/1.14  tff(f_37, axiom, (![A]: ~((![B]: (r2_hidden(B, A) => v3_ordinal1(B))) & (![B]: (v3_ordinal1(B) => ~r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_ordinal1)).
% 1.71/1.14  tff(f_49, negated_conjecture, ~(![A]: ~(![B]: (r2_hidden(B, A) <=> v3_ordinal1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_ordinal1)).
% 1.71/1.14  tff(f_42, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.71/1.14  tff(c_28, plain, (![A_14]: (r2_hidden('#skF_1'(A_14), A_14) | v3_ordinal1('#skF_2'(A_14)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.71/1.14  tff(c_12, plain, (![B_7]: (v3_ordinal1(B_7) | ~r2_hidden(B_7, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.71/1.14  tff(c_37, plain, (v3_ordinal1('#skF_1'('#skF_3')) | v3_ordinal1('#skF_2'('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_12])).
% 1.71/1.14  tff(c_38, plain, (v3_ordinal1('#skF_2'('#skF_3'))), inference(splitLeft, [status(thm)], [c_37])).
% 1.71/1.14  tff(c_39, plain, (![A_15]: (~v3_ordinal1('#skF_1'(A_15)) | r1_tarski(A_15, '#skF_2'(A_15)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.71/1.14  tff(c_14, plain, (![B_7]: (r2_hidden(B_7, '#skF_3') | ~v3_ordinal1(B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.71/1.14  tff(c_22, plain, (![B_11, A_12]: (~r1_tarski(B_11, A_12) | ~r2_hidden(A_12, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.71/1.14  tff(c_26, plain, (![B_7]: (~r1_tarski('#skF_3', B_7) | ~v3_ordinal1(B_7))), inference(resolution, [status(thm)], [c_14, c_22])).
% 1.71/1.14  tff(c_43, plain, (~v3_ordinal1('#skF_2'('#skF_3')) | ~v3_ordinal1('#skF_1'('#skF_3'))), inference(resolution, [status(thm)], [c_39, c_26])).
% 1.71/1.14  tff(c_46, plain, (~v3_ordinal1('#skF_1'('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_43])).
% 1.71/1.14  tff(c_48, plain, (![A_17]: (r2_hidden('#skF_1'(A_17), A_17) | r1_tarski(A_17, '#skF_2'(A_17)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.71/1.14  tff(c_55, plain, (v3_ordinal1('#skF_1'('#skF_3')) | r1_tarski('#skF_3', '#skF_2'('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_12])).
% 1.71/1.14  tff(c_59, plain, (r1_tarski('#skF_3', '#skF_2'('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_55])).
% 1.71/1.14  tff(c_62, plain, (~v3_ordinal1('#skF_2'('#skF_3'))), inference(resolution, [status(thm)], [c_59, c_26])).
% 1.71/1.14  tff(c_66, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_62])).
% 1.71/1.14  tff(c_67, plain, (v3_ordinal1('#skF_1'('#skF_3'))), inference(splitRight, [status(thm)], [c_37])).
% 1.71/1.14  tff(c_6, plain, (![A_1]: (~v3_ordinal1('#skF_1'(A_1)) | v3_ordinal1('#skF_2'(A_1)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.71/1.14  tff(c_68, plain, (~v3_ordinal1('#skF_2'('#skF_3'))), inference(splitRight, [status(thm)], [c_37])).
% 1.71/1.14  tff(c_71, plain, (~v3_ordinal1('#skF_1'('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_68])).
% 1.71/1.14  tff(c_75, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_71])).
% 1.71/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.14  
% 1.71/1.14  Inference rules
% 1.71/1.14  ----------------------
% 1.71/1.14  #Ref     : 0
% 1.71/1.14  #Sup     : 9
% 1.71/1.14  #Fact    : 0
% 1.71/1.14  #Define  : 0
% 1.71/1.14  #Split   : 1
% 1.71/1.14  #Chain   : 0
% 1.71/1.14  #Close   : 0
% 1.71/1.14  
% 1.71/1.14  Ordering : KBO
% 1.71/1.14  
% 1.71/1.14  Simplification rules
% 1.71/1.14  ----------------------
% 1.71/1.14  #Subsume      : 0
% 1.71/1.14  #Demod        : 3
% 1.71/1.14  #Tautology    : 1
% 1.71/1.14  #SimpNegUnit  : 1
% 1.71/1.14  #BackRed      : 0
% 1.71/1.14  
% 1.71/1.14  #Partial instantiations: 0
% 1.71/1.14  #Strategies tried      : 1
% 1.71/1.14  
% 1.71/1.14  Timing (in seconds)
% 1.71/1.14  ----------------------
% 1.71/1.14  Preprocessing        : 0.25
% 1.71/1.14  Parsing              : 0.14
% 1.71/1.14  CNF conversion       : 0.02
% 1.71/1.14  Main loop            : 0.10
% 1.71/1.14  Inferencing          : 0.05
% 1.71/1.14  Reduction            : 0.02
% 1.71/1.14  Demodulation         : 0.01
% 1.71/1.14  BG Simplification    : 0.01
% 1.71/1.14  Subsumption          : 0.01
% 1.71/1.14  Abstraction          : 0.00
% 1.71/1.14  MUC search           : 0.00
% 1.71/1.14  Cooper               : 0.00
% 1.71/1.14  Total                : 0.37
% 1.71/1.14  Index Insertion      : 0.00
% 1.71/1.14  Index Deletion       : 0.00
% 1.71/1.14  Index Matching       : 0.00
% 1.71/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
