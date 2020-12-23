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
% DateTime   : Thu Dec  3 09:53:34 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   29 (  35 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  61 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > #nlpp > k3_tarski > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( ! [C] :
            ( r2_hidden(C,A)
           => r1_xboole_0(C,B) )
       => r1_xboole_0(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(c_26,plain,(
    ~ r1_xboole_0(k3_tarski('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [C_21,A_6] :
      ( r2_hidden(C_21,'#skF_5'(A_6,k3_tarski(A_6),C_21))
      | ~ r2_hidden(C_21,k3_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_73,plain,(
    ! [A_44,C_45] :
      ( r2_hidden('#skF_5'(A_44,k3_tarski(A_44),C_45),A_44)
      | ~ r2_hidden(C_45,k3_tarski(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    ! [C_26] :
      ( r1_xboole_0(C_26,'#skF_7')
      | ~ r2_hidden(C_26,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_87,plain,(
    ! [C_46] :
      ( r1_xboole_0('#skF_5'('#skF_6',k3_tarski('#skF_6'),C_46),'#skF_7')
      | ~ r2_hidden(C_46,k3_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_73,c_28])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_405,plain,(
    ! [C_75,C_76] :
      ( ~ r2_hidden(C_75,'#skF_7')
      | ~ r2_hidden(C_75,'#skF_5'('#skF_6',k3_tarski('#skF_6'),C_76))
      | ~ r2_hidden(C_76,k3_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_441,plain,(
    ! [C_77] :
      ( ~ r2_hidden(C_77,'#skF_7')
      | ~ r2_hidden(C_77,k3_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_12,c_405])).

tff(c_497,plain,(
    ! [B_81] :
      ( ~ r2_hidden('#skF_1'(k3_tarski('#skF_6'),B_81),'#skF_7')
      | r1_xboole_0(k3_tarski('#skF_6'),B_81) ) ),
    inference(resolution,[status(thm)],[c_6,c_441])).

tff(c_501,plain,(
    r1_xboole_0(k3_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_497])).

tff(c_505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_501])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:22:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.35  
% 2.49/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.35  %$ r2_hidden > r1_xboole_0 > #nlpp > k3_tarski > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 2.49/1.35  
% 2.49/1.35  %Foreground sorts:
% 2.49/1.35  
% 2.49/1.35  
% 2.49/1.35  %Background operators:
% 2.49/1.35  
% 2.49/1.35  
% 2.49/1.35  %Foreground operators:
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.49/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.49/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.49/1.35  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.49/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.49/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.49/1.35  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.49/1.35  
% 2.49/1.36  tff(f_61, negated_conjecture, ~(![A, B]: ((![C]: (r2_hidden(C, A) => r1_xboole_0(C, B))) => r1_xboole_0(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_zfmisc_1)).
% 2.49/1.36  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.49/1.36  tff(f_53, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 2.49/1.36  tff(c_26, plain, (~r1_xboole_0(k3_tarski('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.49/1.36  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.49/1.36  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.49/1.36  tff(c_12, plain, (![C_21, A_6]: (r2_hidden(C_21, '#skF_5'(A_6, k3_tarski(A_6), C_21)) | ~r2_hidden(C_21, k3_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.49/1.36  tff(c_73, plain, (![A_44, C_45]: (r2_hidden('#skF_5'(A_44, k3_tarski(A_44), C_45), A_44) | ~r2_hidden(C_45, k3_tarski(A_44)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.49/1.36  tff(c_28, plain, (![C_26]: (r1_xboole_0(C_26, '#skF_7') | ~r2_hidden(C_26, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.49/1.36  tff(c_87, plain, (![C_46]: (r1_xboole_0('#skF_5'('#skF_6', k3_tarski('#skF_6'), C_46), '#skF_7') | ~r2_hidden(C_46, k3_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_73, c_28])).
% 2.49/1.36  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.49/1.36  tff(c_405, plain, (![C_75, C_76]: (~r2_hidden(C_75, '#skF_7') | ~r2_hidden(C_75, '#skF_5'('#skF_6', k3_tarski('#skF_6'), C_76)) | ~r2_hidden(C_76, k3_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_87, c_2])).
% 2.49/1.36  tff(c_441, plain, (![C_77]: (~r2_hidden(C_77, '#skF_7') | ~r2_hidden(C_77, k3_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_12, c_405])).
% 2.49/1.36  tff(c_497, plain, (![B_81]: (~r2_hidden('#skF_1'(k3_tarski('#skF_6'), B_81), '#skF_7') | r1_xboole_0(k3_tarski('#skF_6'), B_81))), inference(resolution, [status(thm)], [c_6, c_441])).
% 2.49/1.36  tff(c_501, plain, (r1_xboole_0(k3_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_4, c_497])).
% 2.49/1.36  tff(c_505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_501])).
% 2.49/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.36  
% 2.49/1.36  Inference rules
% 2.49/1.36  ----------------------
% 2.49/1.36  #Ref     : 0
% 2.49/1.36  #Sup     : 97
% 2.49/1.36  #Fact    : 0
% 2.49/1.36  #Define  : 0
% 2.49/1.36  #Split   : 2
% 2.49/1.36  #Chain   : 0
% 2.49/1.36  #Close   : 0
% 2.49/1.36  
% 2.49/1.36  Ordering : KBO
% 2.49/1.36  
% 2.49/1.36  Simplification rules
% 2.49/1.36  ----------------------
% 2.49/1.36  #Subsume      : 4
% 2.49/1.36  #Demod        : 8
% 2.49/1.36  #Tautology    : 5
% 2.49/1.36  #SimpNegUnit  : 3
% 2.49/1.36  #BackRed      : 3
% 2.49/1.36  
% 2.49/1.36  #Partial instantiations: 0
% 2.49/1.36  #Strategies tried      : 1
% 2.49/1.36  
% 2.49/1.36  Timing (in seconds)
% 2.49/1.36  ----------------------
% 2.66/1.36  Preprocessing        : 0.29
% 2.66/1.36  Parsing              : 0.15
% 2.66/1.36  CNF conversion       : 0.02
% 2.66/1.36  Main loop            : 0.30
% 2.66/1.36  Inferencing          : 0.13
% 2.66/1.36  Reduction            : 0.05
% 2.66/1.36  Demodulation         : 0.03
% 2.66/1.36  BG Simplification    : 0.02
% 2.66/1.36  Subsumption          : 0.07
% 2.66/1.36  Abstraction          : 0.01
% 2.66/1.36  MUC search           : 0.00
% 2.66/1.36  Cooper               : 0.00
% 2.66/1.36  Total                : 0.62
% 2.66/1.36  Index Insertion      : 0.00
% 2.66/1.36  Index Deletion       : 0.00
% 2.66/1.36  Index Matching       : 0.00
% 2.66/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
