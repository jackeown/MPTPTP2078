%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:24 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   36 (  72 expanded)
%              Number of leaves         :   14 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 ( 150 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v3_ordinal1 > #nlpp > #skF_2 > #skF_1 > #skF_4 > #skF_3

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

tff(f_45,axiom,(
    ! [A] :
      ~ ( ! [B] :
            ( r2_hidden(B,A)
           => v3_ordinal1(B) )
        & ! [B] :
            ( v3_ordinal1(B)
           => ~ r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_ordinal1)).

tff(f_33,axiom,(
    ! [A] :
    ? [B] :
    ! [C] :
      ( r2_hidden(C,B)
    <=> ( r2_hidden(C,A)
        & v3_ordinal1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).

tff(f_57,negated_conjecture,(
    ~ ! [A] :
        ~ ! [B] :
            ( v3_ordinal1(B)
           => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_ordinal1)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_35,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_2'(A_22),A_22)
      | v3_ordinal1('#skF_3'(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [C_6,A_1] :
      ( v3_ordinal1(C_6)
      | ~ r2_hidden(C_6,'#skF_1'(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    ! [A_27] :
      ( v3_ordinal1('#skF_2'('#skF_1'(A_27)))
      | v3_ordinal1('#skF_3'('#skF_1'(A_27))) ) ),
    inference(resolution,[status(thm)],[c_35,c_4])).

tff(c_12,plain,(
    ! [A_7] :
      ( ~ v3_ordinal1('#skF_2'(A_7))
      | v3_ordinal1('#skF_3'(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_71,plain,(
    ! [A_27] : v3_ordinal1('#skF_3'('#skF_1'(A_27))) ),
    inference(resolution,[status(thm)],[c_67,c_12])).

tff(c_18,plain,(
    ! [B_13] :
      ( r2_hidden(B_13,'#skF_4')
      | ~ v3_ordinal1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v3_ordinal1('#skF_2'(A_7))
      | r1_tarski(A_7,'#skF_3'(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_75,plain,(
    ! [C_30,A_31] :
      ( r2_hidden(C_30,'#skF_1'(A_31))
      | ~ v3_ordinal1(C_30)
      | ~ r2_hidden(C_30,A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( ~ r1_tarski(B_11,A_10)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_89,plain,(
    ! [A_32,C_33] :
      ( ~ r1_tarski('#skF_1'(A_32),C_33)
      | ~ v3_ordinal1(C_33)
      | ~ r2_hidden(C_33,A_32) ) ),
    inference(resolution,[status(thm)],[c_75,c_16])).

tff(c_93,plain,(
    ! [A_32] :
      ( ~ v3_ordinal1('#skF_3'('#skF_1'(A_32)))
      | ~ r2_hidden('#skF_3'('#skF_1'(A_32)),A_32)
      | ~ v3_ordinal1('#skF_2'('#skF_1'(A_32))) ) ),
    inference(resolution,[status(thm)],[c_8,c_89])).

tff(c_97,plain,(
    ! [A_34] :
      ( ~ r2_hidden('#skF_3'('#skF_1'(A_34)),A_34)
      | ~ v3_ordinal1('#skF_2'('#skF_1'(A_34))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_93])).

tff(c_105,plain,
    ( ~ v3_ordinal1('#skF_2'('#skF_1'('#skF_4')))
    | ~ v3_ordinal1('#skF_3'('#skF_1'('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_18,c_97])).

tff(c_111,plain,(
    ~ v3_ordinal1('#skF_2'('#skF_1'('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_105])).

tff(c_52,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_2'(A_26),A_26)
      | r1_tarski(A_26,'#skF_3'(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_112,plain,(
    ! [A_35] :
      ( v3_ordinal1('#skF_2'('#skF_1'(A_35)))
      | r1_tarski('#skF_1'(A_35),'#skF_3'('#skF_1'(A_35))) ) ),
    inference(resolution,[status(thm)],[c_52,c_4])).

tff(c_87,plain,(
    ! [A_31,C_30] :
      ( ~ r1_tarski('#skF_1'(A_31),C_30)
      | ~ v3_ordinal1(C_30)
      | ~ r2_hidden(C_30,A_31) ) ),
    inference(resolution,[status(thm)],[c_75,c_16])).

tff(c_115,plain,(
    ! [A_35] :
      ( ~ v3_ordinal1('#skF_3'('#skF_1'(A_35)))
      | ~ r2_hidden('#skF_3'('#skF_1'(A_35)),A_35)
      | v3_ordinal1('#skF_2'('#skF_1'(A_35))) ) ),
    inference(resolution,[status(thm)],[c_112,c_87])).

tff(c_119,plain,(
    ! [A_36] :
      ( ~ r2_hidden('#skF_3'('#skF_1'(A_36)),A_36)
      | v3_ordinal1('#skF_2'('#skF_1'(A_36))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_115])).

tff(c_127,plain,
    ( v3_ordinal1('#skF_2'('#skF_1'('#skF_4')))
    | ~ v3_ordinal1('#skF_3'('#skF_1'('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_18,c_119])).

tff(c_133,plain,(
    v3_ordinal1('#skF_2'('#skF_1'('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_127])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.32  % Computer   : n007.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % DateTime   : Tue Dec  1 12:08:21 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.14/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  
% 1.88/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  %$ r2_hidden > r1_tarski > v3_ordinal1 > #nlpp > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 1.88/1.21  
% 1.88/1.21  %Foreground sorts:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Background operators:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Foreground operators:
% 1.88/1.21  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.88/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.21  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.21  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.21  
% 1.88/1.22  tff(f_45, axiom, (![A]: ~((![B]: (r2_hidden(B, A) => v3_ordinal1(B))) & (![B]: (v3_ordinal1(B) => ~r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_ordinal1)).
% 1.88/1.22  tff(f_33, axiom, (![A]: (?[B]: (![C]: (r2_hidden(C, B) <=> (r2_hidden(C, A) & v3_ordinal1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s1_xboole_0__e3_53__ordinal1)).
% 1.88/1.22  tff(f_57, negated_conjecture, ~(![A]: ~(![B]: (v3_ordinal1(B) => r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_ordinal1)).
% 1.88/1.22  tff(f_50, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.88/1.22  tff(c_35, plain, (![A_22]: (r2_hidden('#skF_2'(A_22), A_22) | v3_ordinal1('#skF_3'(A_22)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.88/1.22  tff(c_4, plain, (![C_6, A_1]: (v3_ordinal1(C_6) | ~r2_hidden(C_6, '#skF_1'(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.22  tff(c_67, plain, (![A_27]: (v3_ordinal1('#skF_2'('#skF_1'(A_27))) | v3_ordinal1('#skF_3'('#skF_1'(A_27))))), inference(resolution, [status(thm)], [c_35, c_4])).
% 1.88/1.22  tff(c_12, plain, (![A_7]: (~v3_ordinal1('#skF_2'(A_7)) | v3_ordinal1('#skF_3'(A_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.88/1.22  tff(c_71, plain, (![A_27]: (v3_ordinal1('#skF_3'('#skF_1'(A_27))))), inference(resolution, [status(thm)], [c_67, c_12])).
% 1.88/1.22  tff(c_18, plain, (![B_13]: (r2_hidden(B_13, '#skF_4') | ~v3_ordinal1(B_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.22  tff(c_8, plain, (![A_7]: (~v3_ordinal1('#skF_2'(A_7)) | r1_tarski(A_7, '#skF_3'(A_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.88/1.22  tff(c_75, plain, (![C_30, A_31]: (r2_hidden(C_30, '#skF_1'(A_31)) | ~v3_ordinal1(C_30) | ~r2_hidden(C_30, A_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.22  tff(c_16, plain, (![B_11, A_10]: (~r1_tarski(B_11, A_10) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.88/1.22  tff(c_89, plain, (![A_32, C_33]: (~r1_tarski('#skF_1'(A_32), C_33) | ~v3_ordinal1(C_33) | ~r2_hidden(C_33, A_32))), inference(resolution, [status(thm)], [c_75, c_16])).
% 1.88/1.22  tff(c_93, plain, (![A_32]: (~v3_ordinal1('#skF_3'('#skF_1'(A_32))) | ~r2_hidden('#skF_3'('#skF_1'(A_32)), A_32) | ~v3_ordinal1('#skF_2'('#skF_1'(A_32))))), inference(resolution, [status(thm)], [c_8, c_89])).
% 1.88/1.22  tff(c_97, plain, (![A_34]: (~r2_hidden('#skF_3'('#skF_1'(A_34)), A_34) | ~v3_ordinal1('#skF_2'('#skF_1'(A_34))))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_93])).
% 1.88/1.22  tff(c_105, plain, (~v3_ordinal1('#skF_2'('#skF_1'('#skF_4'))) | ~v3_ordinal1('#skF_3'('#skF_1'('#skF_4')))), inference(resolution, [status(thm)], [c_18, c_97])).
% 1.88/1.22  tff(c_111, plain, (~v3_ordinal1('#skF_2'('#skF_1'('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_105])).
% 1.88/1.22  tff(c_52, plain, (![A_26]: (r2_hidden('#skF_2'(A_26), A_26) | r1_tarski(A_26, '#skF_3'(A_26)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.88/1.22  tff(c_112, plain, (![A_35]: (v3_ordinal1('#skF_2'('#skF_1'(A_35))) | r1_tarski('#skF_1'(A_35), '#skF_3'('#skF_1'(A_35))))), inference(resolution, [status(thm)], [c_52, c_4])).
% 1.88/1.22  tff(c_87, plain, (![A_31, C_30]: (~r1_tarski('#skF_1'(A_31), C_30) | ~v3_ordinal1(C_30) | ~r2_hidden(C_30, A_31))), inference(resolution, [status(thm)], [c_75, c_16])).
% 1.88/1.22  tff(c_115, plain, (![A_35]: (~v3_ordinal1('#skF_3'('#skF_1'(A_35))) | ~r2_hidden('#skF_3'('#skF_1'(A_35)), A_35) | v3_ordinal1('#skF_2'('#skF_1'(A_35))))), inference(resolution, [status(thm)], [c_112, c_87])).
% 1.88/1.22  tff(c_119, plain, (![A_36]: (~r2_hidden('#skF_3'('#skF_1'(A_36)), A_36) | v3_ordinal1('#skF_2'('#skF_1'(A_36))))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_115])).
% 1.88/1.22  tff(c_127, plain, (v3_ordinal1('#skF_2'('#skF_1'('#skF_4'))) | ~v3_ordinal1('#skF_3'('#skF_1'('#skF_4')))), inference(resolution, [status(thm)], [c_18, c_119])).
% 1.88/1.22  tff(c_133, plain, (v3_ordinal1('#skF_2'('#skF_1'('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_127])).
% 1.88/1.22  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_133])).
% 1.88/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.22  
% 1.88/1.22  Inference rules
% 1.88/1.22  ----------------------
% 1.88/1.22  #Ref     : 0
% 1.88/1.22  #Sup     : 18
% 1.88/1.22  #Fact    : 0
% 1.88/1.22  #Define  : 0
% 1.88/1.22  #Split   : 1
% 1.88/1.22  #Chain   : 0
% 1.88/1.22  #Close   : 0
% 1.88/1.22  
% 1.88/1.22  Ordering : KBO
% 1.88/1.22  
% 1.88/1.22  Simplification rules
% 1.88/1.22  ----------------------
% 1.88/1.22  #Subsume      : 0
% 1.88/1.22  #Demod        : 8
% 1.88/1.22  #Tautology    : 4
% 1.88/1.22  #SimpNegUnit  : 1
% 1.88/1.22  #BackRed      : 0
% 1.88/1.22  
% 1.88/1.22  #Partial instantiations: 0
% 1.88/1.22  #Strategies tried      : 1
% 1.88/1.22  
% 1.88/1.22  Timing (in seconds)
% 1.88/1.22  ----------------------
% 1.88/1.22  Preprocessing        : 0.28
% 1.88/1.22  Parsing              : 0.16
% 1.88/1.22  CNF conversion       : 0.02
% 1.88/1.22  Main loop            : 0.16
% 1.88/1.22  Inferencing          : 0.08
% 1.88/1.22  Reduction            : 0.03
% 1.88/1.22  Demodulation         : 0.02
% 1.88/1.22  BG Simplification    : 0.01
% 1.88/1.22  Subsumption          : 0.03
% 1.88/1.22  Abstraction          : 0.01
% 1.88/1.22  MUC search           : 0.00
% 1.88/1.23  Cooper               : 0.00
% 1.88/1.23  Total                : 0.48
% 1.88/1.23  Index Insertion      : 0.00
% 1.88/1.23  Index Deletion       : 0.00
% 1.88/1.23  Index Matching       : 0.00
% 1.88/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
