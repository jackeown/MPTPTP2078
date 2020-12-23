%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:24 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   33 (  68 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 ( 127 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v3_ordinal1 > #nlpp > #skF_2 > #skF_1 > #skF_4 > #skF_3

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

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_39,axiom,(
    ! [A] :
      ~ ! [B] :
          ( r2_hidden(B,A)
        <=> v3_ordinal1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_ordinal1)).

tff(f_33,axiom,(
    ! [A] :
    ? [B] :
    ! [C] :
      ( r2_hidden(C,B)
    <=> ( r2_hidden(C,A)
        & v3_ordinal1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).

tff(f_46,negated_conjecture,(
    ~ ! [A] :
        ~ ! [B] :
            ( v3_ordinal1(B)
           => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_ordinal1)).

tff(c_20,plain,(
    ! [A_15] :
      ( v3_ordinal1('#skF_2'(A_15))
      | r2_hidden('#skF_3'(A_15),A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [C_6,A_1] :
      ( v3_ordinal1(C_6)
      | ~ r2_hidden(C_6,'#skF_1'(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_25,plain,(
    ! [A_1] :
      ( v3_ordinal1('#skF_3'('#skF_1'(A_1)))
      | v3_ordinal1('#skF_2'('#skF_1'(A_1))) ) ),
    inference(resolution,[status(thm)],[c_20,c_4])).

tff(c_16,plain,(
    ! [B_10] :
      ( r2_hidden(B_10,'#skF_4')
      | ~ v3_ordinal1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    ! [C_21,A_22] :
      ( r2_hidden(C_21,'#skF_1'(A_22))
      | ~ v3_ordinal1(C_21)
      | ~ r2_hidden(C_21,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ r2_hidden('#skF_2'(A_7),A_7)
      | ~ v3_ordinal1('#skF_3'(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_91,plain,(
    ! [A_25] :
      ( ~ v3_ordinal1('#skF_3'('#skF_1'(A_25)))
      | ~ v3_ordinal1('#skF_2'('#skF_1'(A_25)))
      | ~ r2_hidden('#skF_2'('#skF_1'(A_25)),A_25) ) ),
    inference(resolution,[status(thm)],[c_50,c_8])).

tff(c_101,plain,
    ( ~ v3_ordinal1('#skF_3'('#skF_1'('#skF_4')))
    | ~ v3_ordinal1('#skF_2'('#skF_1'('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_16,c_91])).

tff(c_111,plain,(
    ~ v3_ordinal1('#skF_2'('#skF_1'('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_118,plain,(
    v3_ordinal1('#skF_3'('#skF_1'('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_25,c_111])).

tff(c_10,plain,(
    ! [A_7] :
      ( v3_ordinal1('#skF_2'(A_7))
      | ~ v3_ordinal1('#skF_3'(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_119,plain,(
    ~ v3_ordinal1('#skF_3'('#skF_1'('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_10,c_111])).

tff(c_121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_119])).

tff(c_122,plain,(
    ~ v3_ordinal1('#skF_3'('#skF_1'('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_123,plain,(
    v3_ordinal1('#skF_2'('#skF_1'('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_12,plain,(
    ! [A_7] :
      ( ~ r2_hidden('#skF_2'(A_7),A_7)
      | r2_hidden('#skF_3'(A_7),A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_102,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_3'('#skF_1'(A_26)),'#skF_1'(A_26))
      | ~ v3_ordinal1('#skF_2'('#skF_1'(A_26)))
      | ~ r2_hidden('#skF_2'('#skF_1'(A_26)),A_26) ) ),
    inference(resolution,[status(thm)],[c_50,c_12])).

tff(c_124,plain,(
    ! [A_27] :
      ( v3_ordinal1('#skF_3'('#skF_1'(A_27)))
      | ~ v3_ordinal1('#skF_2'('#skF_1'(A_27)))
      | ~ r2_hidden('#skF_2'('#skF_1'(A_27)),A_27) ) ),
    inference(resolution,[status(thm)],[c_102,c_4])).

tff(c_132,plain,
    ( v3_ordinal1('#skF_3'('#skF_1'('#skF_4')))
    | ~ v3_ordinal1('#skF_2'('#skF_1'('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_16,c_124])).

tff(c_136,plain,(
    v3_ordinal1('#skF_3'('#skF_1'('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_132])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:34:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.23  
% 1.89/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.23  %$ r2_hidden > v3_ordinal1 > #nlpp > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 1.91/1.23  
% 1.91/1.23  %Foreground sorts:
% 1.91/1.23  
% 1.91/1.23  
% 1.91/1.23  %Background operators:
% 1.91/1.23  
% 1.91/1.23  
% 1.91/1.23  %Foreground operators:
% 1.91/1.23  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.91/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.91/1.23  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.91/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.23  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.91/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.23  
% 1.91/1.24  tff(f_39, axiom, (![A]: ~(![B]: (r2_hidden(B, A) <=> v3_ordinal1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_ordinal1)).
% 1.91/1.24  tff(f_33, axiom, (![A]: (?[B]: (![C]: (r2_hidden(C, B) <=> (r2_hidden(C, A) & v3_ordinal1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s1_xboole_0__e3_53__ordinal1)).
% 1.91/1.24  tff(f_46, negated_conjecture, ~(![A]: ~(![B]: (v3_ordinal1(B) => r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_ordinal1)).
% 1.91/1.24  tff(c_20, plain, (![A_15]: (v3_ordinal1('#skF_2'(A_15)) | r2_hidden('#skF_3'(A_15), A_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.91/1.24  tff(c_4, plain, (![C_6, A_1]: (v3_ordinal1(C_6) | ~r2_hidden(C_6, '#skF_1'(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.91/1.24  tff(c_25, plain, (![A_1]: (v3_ordinal1('#skF_3'('#skF_1'(A_1))) | v3_ordinal1('#skF_2'('#skF_1'(A_1))))), inference(resolution, [status(thm)], [c_20, c_4])).
% 1.91/1.24  tff(c_16, plain, (![B_10]: (r2_hidden(B_10, '#skF_4') | ~v3_ordinal1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.91/1.24  tff(c_50, plain, (![C_21, A_22]: (r2_hidden(C_21, '#skF_1'(A_22)) | ~v3_ordinal1(C_21) | ~r2_hidden(C_21, A_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.91/1.24  tff(c_8, plain, (![A_7]: (~r2_hidden('#skF_2'(A_7), A_7) | ~v3_ordinal1('#skF_3'(A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.91/1.24  tff(c_91, plain, (![A_25]: (~v3_ordinal1('#skF_3'('#skF_1'(A_25))) | ~v3_ordinal1('#skF_2'('#skF_1'(A_25))) | ~r2_hidden('#skF_2'('#skF_1'(A_25)), A_25))), inference(resolution, [status(thm)], [c_50, c_8])).
% 1.91/1.24  tff(c_101, plain, (~v3_ordinal1('#skF_3'('#skF_1'('#skF_4'))) | ~v3_ordinal1('#skF_2'('#skF_1'('#skF_4')))), inference(resolution, [status(thm)], [c_16, c_91])).
% 1.91/1.24  tff(c_111, plain, (~v3_ordinal1('#skF_2'('#skF_1'('#skF_4')))), inference(splitLeft, [status(thm)], [c_101])).
% 1.91/1.24  tff(c_118, plain, (v3_ordinal1('#skF_3'('#skF_1'('#skF_4')))), inference(resolution, [status(thm)], [c_25, c_111])).
% 1.91/1.24  tff(c_10, plain, (![A_7]: (v3_ordinal1('#skF_2'(A_7)) | ~v3_ordinal1('#skF_3'(A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.91/1.24  tff(c_119, plain, (~v3_ordinal1('#skF_3'('#skF_1'('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_111])).
% 1.91/1.24  tff(c_121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_119])).
% 1.91/1.24  tff(c_122, plain, (~v3_ordinal1('#skF_3'('#skF_1'('#skF_4')))), inference(splitRight, [status(thm)], [c_101])).
% 1.91/1.24  tff(c_123, plain, (v3_ordinal1('#skF_2'('#skF_1'('#skF_4')))), inference(splitRight, [status(thm)], [c_101])).
% 1.91/1.24  tff(c_12, plain, (![A_7]: (~r2_hidden('#skF_2'(A_7), A_7) | r2_hidden('#skF_3'(A_7), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.91/1.24  tff(c_102, plain, (![A_26]: (r2_hidden('#skF_3'('#skF_1'(A_26)), '#skF_1'(A_26)) | ~v3_ordinal1('#skF_2'('#skF_1'(A_26))) | ~r2_hidden('#skF_2'('#skF_1'(A_26)), A_26))), inference(resolution, [status(thm)], [c_50, c_12])).
% 1.91/1.24  tff(c_124, plain, (![A_27]: (v3_ordinal1('#skF_3'('#skF_1'(A_27))) | ~v3_ordinal1('#skF_2'('#skF_1'(A_27))) | ~r2_hidden('#skF_2'('#skF_1'(A_27)), A_27))), inference(resolution, [status(thm)], [c_102, c_4])).
% 1.91/1.24  tff(c_132, plain, (v3_ordinal1('#skF_3'('#skF_1'('#skF_4'))) | ~v3_ordinal1('#skF_2'('#skF_1'('#skF_4')))), inference(resolution, [status(thm)], [c_16, c_124])).
% 1.91/1.24  tff(c_136, plain, (v3_ordinal1('#skF_3'('#skF_1'('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_132])).
% 1.91/1.24  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_136])).
% 1.91/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.24  
% 1.91/1.24  Inference rules
% 1.91/1.24  ----------------------
% 1.91/1.24  #Ref     : 0
% 1.91/1.24  #Sup     : 21
% 1.91/1.24  #Fact    : 0
% 1.91/1.24  #Define  : 0
% 1.91/1.24  #Split   : 2
% 1.91/1.24  #Chain   : 0
% 1.91/1.24  #Close   : 0
% 1.91/1.24  
% 1.91/1.24  Ordering : KBO
% 1.91/1.24  
% 1.91/1.24  Simplification rules
% 1.91/1.24  ----------------------
% 1.91/1.24  #Subsume      : 3
% 1.91/1.24  #Demod        : 2
% 1.91/1.24  #Tautology    : 2
% 1.91/1.24  #SimpNegUnit  : 1
% 1.91/1.24  #BackRed      : 0
% 1.91/1.24  
% 1.91/1.24  #Partial instantiations: 0
% 1.91/1.24  #Strategies tried      : 1
% 1.91/1.24  
% 1.91/1.24  Timing (in seconds)
% 1.91/1.24  ----------------------
% 1.91/1.25  Preprocessing        : 0.27
% 1.91/1.25  Parsing              : 0.15
% 1.91/1.25  CNF conversion       : 0.02
% 1.91/1.25  Main loop            : 0.16
% 1.91/1.25  Inferencing          : 0.08
% 1.91/1.25  Reduction            : 0.02
% 1.91/1.25  Demodulation         : 0.02
% 1.91/1.25  BG Simplification    : 0.01
% 1.91/1.25  Subsumption          : 0.03
% 1.91/1.25  Abstraction          : 0.01
% 1.91/1.25  MUC search           : 0.00
% 1.91/1.25  Cooper               : 0.00
% 1.91/1.25  Total                : 0.46
% 1.91/1.25  Index Insertion      : 0.00
% 1.91/1.25  Index Deletion       : 0.00
% 1.91/1.25  Index Matching       : 0.00
% 1.91/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
