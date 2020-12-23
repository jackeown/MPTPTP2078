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
% DateTime   : Thu Dec  3 09:52:01 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  32 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
     => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(c_4,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_54,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_xboole_0(A_23,C_24)
      | ~ r1_xboole_0(A_23,k2_xboole_0(B_25,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_57,plain,(
    ! [A_23] :
      ( r1_xboole_0(A_23,'#skF_3')
      | ~ r1_xboole_0(A_23,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_54])).

tff(c_60,plain,(
    ! [A_26] : r1_xboole_0(A_26,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_57])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden(A_7,B_8)
      | ~ r1_xboole_0(k1_tarski(A_7),B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_65,plain,(
    ! [A_7] : ~ r2_hidden(A_7,'#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_14])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_67,plain,(
    ! [A_28,C_29,B_30] :
      ( r2_hidden(A_28,C_29)
      | ~ r1_tarski(k2_xboole_0(k2_tarski(A_28,B_30),C_29),C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_70,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_67])).

tff(c_75,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_70])).

tff(c_77,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.32  % Computer   : n023.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % DateTime   : Tue Dec  1 14:49:36 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.10  
% 1.67/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.10  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.67/1.10  
% 1.67/1.10  %Foreground sorts:
% 1.67/1.10  
% 1.67/1.10  
% 1.67/1.10  %Background operators:
% 1.67/1.10  
% 1.67/1.10  
% 1.67/1.10  %Foreground operators:
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.67/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.67/1.10  
% 1.67/1.11  tff(f_29, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.67/1.11  tff(f_60, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 1.67/1.11  tff(f_45, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 1.67/1.11  tff(f_52, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.67/1.11  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.67/1.11  tff(f_56, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 1.67/1.11  tff(c_4, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.11  tff(c_18, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.67/1.11  tff(c_54, plain, (![A_23, C_24, B_25]: (r1_xboole_0(A_23, C_24) | ~r1_xboole_0(A_23, k2_xboole_0(B_25, C_24)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.67/1.11  tff(c_57, plain, (![A_23]: (r1_xboole_0(A_23, '#skF_3') | ~r1_xboole_0(A_23, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_54])).
% 1.67/1.11  tff(c_60, plain, (![A_26]: (r1_xboole_0(A_26, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_57])).
% 1.67/1.11  tff(c_14, plain, (![A_7, B_8]: (~r2_hidden(A_7, B_8) | ~r1_xboole_0(k1_tarski(A_7), B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.67/1.11  tff(c_65, plain, (![A_7]: (~r2_hidden(A_7, '#skF_3'))), inference(resolution, [status(thm)], [c_60, c_14])).
% 1.67/1.11  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.11  tff(c_67, plain, (![A_28, C_29, B_30]: (r2_hidden(A_28, C_29) | ~r1_tarski(k2_xboole_0(k2_tarski(A_28, B_30), C_29), C_29))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.11  tff(c_70, plain, (r2_hidden('#skF_1', '#skF_3') | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_67])).
% 1.67/1.11  tff(c_75, plain, (r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_70])).
% 1.67/1.11  tff(c_77, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_75])).
% 1.67/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.11  
% 1.67/1.11  Inference rules
% 1.67/1.11  ----------------------
% 1.67/1.11  #Ref     : 0
% 1.67/1.11  #Sup     : 11
% 1.67/1.11  #Fact    : 0
% 1.67/1.11  #Define  : 0
% 1.67/1.11  #Split   : 0
% 1.67/1.11  #Chain   : 0
% 1.67/1.11  #Close   : 0
% 1.67/1.11  
% 1.67/1.11  Ordering : KBO
% 1.67/1.11  
% 1.67/1.11  Simplification rules
% 1.67/1.11  ----------------------
% 1.67/1.11  #Subsume      : 0
% 1.67/1.11  #Demod        : 3
% 1.67/1.11  #Tautology    : 4
% 1.67/1.11  #SimpNegUnit  : 1
% 1.67/1.11  #BackRed      : 0
% 1.67/1.11  
% 1.67/1.11  #Partial instantiations: 0
% 1.67/1.11  #Strategies tried      : 1
% 1.67/1.11  
% 1.67/1.11  Timing (in seconds)
% 1.67/1.11  ----------------------
% 1.67/1.11  Preprocessing        : 0.28
% 1.67/1.11  Parsing              : 0.15
% 1.67/1.11  CNF conversion       : 0.02
% 1.67/1.11  Main loop            : 0.09
% 1.67/1.11  Inferencing          : 0.04
% 1.67/1.11  Reduction            : 0.03
% 1.67/1.11  Demodulation         : 0.02
% 1.67/1.11  BG Simplification    : 0.01
% 1.67/1.11  Subsumption          : 0.01
% 1.67/1.11  Abstraction          : 0.01
% 1.67/1.11  MUC search           : 0.00
% 1.67/1.11  Cooper               : 0.00
% 1.67/1.11  Total                : 0.39
% 1.67/1.11  Index Insertion      : 0.00
% 1.67/1.11  Index Deletion       : 0.00
% 1.67/1.11  Index Matching       : 0.00
% 1.67/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
