%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:04 EST 2020

% Result     : Theorem 4.40s
% Output     : CNFRefutation 4.53s
% Verified   : 
% Statistics : Number of formulae       :   28 (  33 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   33 (  53 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_52,axiom,(
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

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_59,plain,(
    ! [D_23,B_24,A_25] :
      ( r2_hidden(D_23,B_24)
      | ~ r2_hidden(D_23,k3_xboole_0(A_25,B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_69,plain,(
    ! [A_25,B_24,B_8] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_25,B_24),B_8),B_24)
      | r1_xboole_0(k3_xboole_0(A_25,B_24),B_8) ) ),
    inference(resolution,[status(thm)],[c_24,c_59])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_206,plain,(
    ! [A_51,A_52,B_53] :
      ( r2_hidden('#skF_3'(A_51,k3_xboole_0(A_52,B_53)),B_53)
      | r1_xboole_0(A_51,k3_xboole_0(A_52,B_53)) ) ),
    inference(resolution,[status(thm)],[c_22,c_59])).

tff(c_30,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_70,plain,(
    ! [A_26,B_27,C_28] :
      ( ~ r1_xboole_0(A_26,B_27)
      | ~ r2_hidden(C_28,B_27)
      | ~ r2_hidden(C_28,A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_73,plain,(
    ! [C_28] :
      ( ~ r2_hidden(C_28,'#skF_5')
      | ~ r2_hidden(C_28,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_70])).

tff(c_1084,plain,(
    ! [A_125,A_126] :
      ( ~ r2_hidden('#skF_3'(A_125,k3_xboole_0(A_126,'#skF_5')),'#skF_4')
      | r1_xboole_0(A_125,k3_xboole_0(A_126,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_206,c_73])).

tff(c_1102,plain,(
    ! [A_25,A_126] : r1_xboole_0(k3_xboole_0(A_25,'#skF_4'),k3_xboole_0(A_126,'#skF_5')) ),
    inference(resolution,[status(thm)],[c_69,c_1084])).

tff(c_28,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_6','#skF_4'),k3_xboole_0('#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1102,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:18:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.40/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.40/2.11  
% 4.40/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.40/2.11  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.40/2.11  
% 4.40/2.11  %Foreground sorts:
% 4.40/2.11  
% 4.40/2.11  
% 4.40/2.11  %Background operators:
% 4.40/2.11  
% 4.40/2.11  
% 4.40/2.11  %Foreground operators:
% 4.40/2.11  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.40/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.40/2.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.40/2.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.40/2.11  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.40/2.11  tff('#skF_5', type, '#skF_5': $i).
% 4.40/2.11  tff('#skF_6', type, '#skF_6': $i).
% 4.40/2.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.40/2.11  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.40/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.40/2.11  tff('#skF_4', type, '#skF_4': $i).
% 4.40/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.40/2.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.40/2.11  
% 4.53/2.12  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.53/2.12  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.53/2.12  tff(f_59, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 4.53/2.12  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.53/2.12  tff(c_59, plain, (![D_23, B_24, A_25]: (r2_hidden(D_23, B_24) | ~r2_hidden(D_23, k3_xboole_0(A_25, B_24)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.53/2.12  tff(c_69, plain, (![A_25, B_24, B_8]: (r2_hidden('#skF_3'(k3_xboole_0(A_25, B_24), B_8), B_24) | r1_xboole_0(k3_xboole_0(A_25, B_24), B_8))), inference(resolution, [status(thm)], [c_24, c_59])).
% 4.53/2.12  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.53/2.12  tff(c_206, plain, (![A_51, A_52, B_53]: (r2_hidden('#skF_3'(A_51, k3_xboole_0(A_52, B_53)), B_53) | r1_xboole_0(A_51, k3_xboole_0(A_52, B_53)))), inference(resolution, [status(thm)], [c_22, c_59])).
% 4.53/2.12  tff(c_30, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.53/2.12  tff(c_70, plain, (![A_26, B_27, C_28]: (~r1_xboole_0(A_26, B_27) | ~r2_hidden(C_28, B_27) | ~r2_hidden(C_28, A_26))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.53/2.12  tff(c_73, plain, (![C_28]: (~r2_hidden(C_28, '#skF_5') | ~r2_hidden(C_28, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_70])).
% 4.53/2.12  tff(c_1084, plain, (![A_125, A_126]: (~r2_hidden('#skF_3'(A_125, k3_xboole_0(A_126, '#skF_5')), '#skF_4') | r1_xboole_0(A_125, k3_xboole_0(A_126, '#skF_5')))), inference(resolution, [status(thm)], [c_206, c_73])).
% 4.53/2.12  tff(c_1102, plain, (![A_25, A_126]: (r1_xboole_0(k3_xboole_0(A_25, '#skF_4'), k3_xboole_0(A_126, '#skF_5')))), inference(resolution, [status(thm)], [c_69, c_1084])).
% 4.53/2.12  tff(c_28, plain, (~r1_xboole_0(k3_xboole_0('#skF_6', '#skF_4'), k3_xboole_0('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.53/2.12  tff(c_1116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1102, c_28])).
% 4.53/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/2.12  
% 4.53/2.12  Inference rules
% 4.53/2.12  ----------------------
% 4.53/2.12  #Ref     : 0
% 4.53/2.12  #Sup     : 234
% 4.53/2.12  #Fact    : 0
% 4.53/2.12  #Define  : 0
% 4.53/2.12  #Split   : 0
% 4.53/2.12  #Chain   : 0
% 4.53/2.12  #Close   : 0
% 4.53/2.12  
% 4.53/2.13  Ordering : KBO
% 4.53/2.13  
% 4.53/2.13  Simplification rules
% 4.53/2.13  ----------------------
% 4.53/2.13  #Subsume      : 21
% 4.53/2.13  #Demod        : 6
% 4.53/2.13  #Tautology    : 11
% 4.53/2.13  #SimpNegUnit  : 0
% 4.53/2.13  #BackRed      : 1
% 4.53/2.13  
% 4.53/2.13  #Partial instantiations: 0
% 4.53/2.13  #Strategies tried      : 1
% 4.53/2.13  
% 4.53/2.13  Timing (in seconds)
% 4.53/2.13  ----------------------
% 4.61/2.13  Preprocessing        : 0.43
% 4.61/2.13  Parsing              : 0.22
% 4.61/2.13  CNF conversion       : 0.03
% 4.61/2.13  Main loop            : 0.79
% 4.61/2.13  Inferencing          : 0.28
% 4.61/2.13  Reduction            : 0.19
% 4.61/2.13  Demodulation         : 0.14
% 4.61/2.13  BG Simplification    : 0.04
% 4.61/2.13  Subsumption          : 0.22
% 4.61/2.13  Abstraction          : 0.04
% 4.61/2.13  MUC search           : 0.00
% 4.61/2.13  Cooper               : 0.00
% 4.61/2.13  Total                : 1.26
% 4.61/2.13  Index Insertion      : 0.00
% 4.61/2.13  Index Deletion       : 0.00
% 4.61/2.13  Index Matching       : 0.00
% 4.61/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
