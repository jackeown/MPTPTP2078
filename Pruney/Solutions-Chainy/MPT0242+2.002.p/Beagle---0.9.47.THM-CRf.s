%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:54 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   32 (  46 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  58 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_34,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),B)
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_8,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_13,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_12,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | ~ r1_tarski(k1_tarski(A_5),B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_16])).

tff(c_27,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13,c_22])).

tff(c_28,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(k1_tarski(A_1),B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_29,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_10,plain,
    ( ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2')
    | r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_40,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_10])).

tff(c_43,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_40])).

tff(c_47,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_43])).

tff(c_48,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_49,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_6,plain,
    ( ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_58,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_6])).

tff(c_61,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_58])).

tff(c_65,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.20  
% 1.58/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.21  %$ r2_hidden > r1_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.58/1.21  
% 1.58/1.21  %Foreground sorts:
% 1.58/1.21  
% 1.58/1.21  
% 1.58/1.21  %Background operators:
% 1.58/1.21  
% 1.58/1.21  
% 1.58/1.21  %Foreground operators:
% 1.58/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.58/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.58/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.58/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.58/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.58/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.58/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.21  
% 1.58/1.22  tff(f_34, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 1.58/1.22  tff(f_29, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.58/1.22  tff(c_8, plain, (r2_hidden('#skF_1', '#skF_2') | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.58/1.22  tff(c_13, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_8])).
% 1.58/1.22  tff(c_12, plain, (r2_hidden('#skF_1', '#skF_2') | r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.58/1.22  tff(c_14, plain, (r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_12])).
% 1.58/1.22  tff(c_16, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | ~r1_tarski(k1_tarski(A_5), B_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.58/1.22  tff(c_22, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_14, c_16])).
% 1.58/1.22  tff(c_27, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13, c_22])).
% 1.58/1.22  tff(c_28, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_12])).
% 1.58/1.22  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(k1_tarski(A_1), B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.58/1.22  tff(c_29, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_12])).
% 1.58/1.22  tff(c_10, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2') | r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.58/1.22  tff(c_40, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_29, c_10])).
% 1.58/1.22  tff(c_43, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4, c_40])).
% 1.58/1.22  tff(c_47, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_43])).
% 1.58/1.22  tff(c_48, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_8])).
% 1.58/1.22  tff(c_49, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_8])).
% 1.58/1.22  tff(c_6, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2') | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.58/1.22  tff(c_58, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_6])).
% 1.58/1.22  tff(c_61, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4, c_58])).
% 1.58/1.22  tff(c_65, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_61])).
% 1.58/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.22  
% 1.58/1.22  Inference rules
% 1.58/1.22  ----------------------
% 1.58/1.22  #Ref     : 0
% 1.58/1.22  #Sup     : 7
% 1.58/1.22  #Fact    : 0
% 1.58/1.22  #Define  : 0
% 1.58/1.22  #Split   : 2
% 1.58/1.22  #Chain   : 0
% 1.58/1.22  #Close   : 0
% 1.58/1.22  
% 1.58/1.22  Ordering : KBO
% 1.58/1.22  
% 1.58/1.22  Simplification rules
% 1.58/1.22  ----------------------
% 1.58/1.22  #Subsume      : 3
% 1.58/1.22  #Demod        : 4
% 1.58/1.22  #Tautology    : 4
% 1.58/1.22  #SimpNegUnit  : 2
% 1.58/1.22  #BackRed      : 0
% 1.58/1.22  
% 1.58/1.22  #Partial instantiations: 0
% 1.58/1.22  #Strategies tried      : 1
% 1.58/1.22  
% 1.58/1.22  Timing (in seconds)
% 1.58/1.22  ----------------------
% 1.67/1.22  Preprocessing        : 0.25
% 1.67/1.22  Parsing              : 0.14
% 1.67/1.22  CNF conversion       : 0.02
% 1.67/1.22  Main loop            : 0.09
% 1.67/1.22  Inferencing          : 0.03
% 1.67/1.22  Reduction            : 0.02
% 1.67/1.22  Demodulation         : 0.01
% 1.67/1.22  BG Simplification    : 0.01
% 1.67/1.22  Subsumption          : 0.01
% 1.67/1.22  Abstraction          : 0.00
% 1.67/1.22  MUC search           : 0.00
% 1.67/1.22  Cooper               : 0.00
% 1.67/1.22  Total                : 0.37
% 1.67/1.22  Index Insertion      : 0.00
% 1.67/1.22  Index Deletion       : 0.00
% 1.67/1.22  Index Matching       : 0.00
% 1.67/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
