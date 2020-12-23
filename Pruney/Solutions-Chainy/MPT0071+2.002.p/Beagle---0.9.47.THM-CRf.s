%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:23 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   30 (  37 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  74 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > #nlpp > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D)
          & r1_xboole_0(B,D) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

tff(f_50,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_20,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_31,plain,(
    ! [C_20,B_21,A_22] :
      ( r2_hidden(C_20,B_21)
      | ~ r2_hidden(C_20,A_22)
      | ~ r1_tarski(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_39,plain,(
    ! [A_6,B_7,B_21] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_21)
      | ~ r1_tarski(A_6,B_21)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_31])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_119,plain,(
    ! [A_37,B_38,B_39] :
      ( r2_hidden('#skF_2'(A_37,B_38),B_39)
      | ~ r1_tarski(B_38,B_39)
      | r1_xboole_0(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_10,c_31])).

tff(c_16,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_41,plain,(
    ! [A_23,B_24,C_25] :
      ( ~ r1_xboole_0(A_23,B_24)
      | ~ r2_hidden(C_25,B_24)
      | ~ r2_hidden(C_25,A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_44,plain,(
    ! [C_25] :
      ( ~ r2_hidden(C_25,'#skF_6')
      | ~ r2_hidden(C_25,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_41])).

tff(c_180,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden('#skF_2'(A_46,B_47),'#skF_4')
      | ~ r1_tarski(B_47,'#skF_6')
      | r1_xboole_0(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_119,c_44])).

tff(c_219,plain,(
    ! [B_52,A_53] :
      ( ~ r1_tarski(B_52,'#skF_6')
      | ~ r1_tarski(A_53,'#skF_4')
      | r1_xboole_0(A_53,B_52) ) ),
    inference(resolution,[status(thm)],[c_39,c_180])).

tff(c_14,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_224,plain,
    ( ~ r1_tarski('#skF_5','#skF_6')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_219,c_14])).

tff(c_229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_224])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:52:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.21  
% 1.93/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.21  %$ r2_hidden > r1_xboole_0 > r1_tarski > #nlpp > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.93/1.21  
% 1.93/1.21  %Foreground sorts:
% 1.93/1.21  
% 1.93/1.21  
% 1.93/1.21  %Background operators:
% 1.93/1.21  
% 1.93/1.21  
% 1.93/1.21  %Foreground operators:
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.93/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.93/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.93/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.93/1.21  
% 2.07/1.22  tff(f_59, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 2.07/1.22  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.07/1.22  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.07/1.22  tff(c_20, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.07/1.22  tff(c_18, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.07/1.22  tff(c_12, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.22  tff(c_31, plain, (![C_20, B_21, A_22]: (r2_hidden(C_20, B_21) | ~r2_hidden(C_20, A_22) | ~r1_tarski(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.07/1.22  tff(c_39, plain, (![A_6, B_7, B_21]: (r2_hidden('#skF_2'(A_6, B_7), B_21) | ~r1_tarski(A_6, B_21) | r1_xboole_0(A_6, B_7))), inference(resolution, [status(thm)], [c_12, c_31])).
% 2.07/1.22  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.22  tff(c_119, plain, (![A_37, B_38, B_39]: (r2_hidden('#skF_2'(A_37, B_38), B_39) | ~r1_tarski(B_38, B_39) | r1_xboole_0(A_37, B_38))), inference(resolution, [status(thm)], [c_10, c_31])).
% 2.07/1.22  tff(c_16, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.07/1.22  tff(c_41, plain, (![A_23, B_24, C_25]: (~r1_xboole_0(A_23, B_24) | ~r2_hidden(C_25, B_24) | ~r2_hidden(C_25, A_23))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.22  tff(c_44, plain, (![C_25]: (~r2_hidden(C_25, '#skF_6') | ~r2_hidden(C_25, '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_41])).
% 2.07/1.22  tff(c_180, plain, (![A_46, B_47]: (~r2_hidden('#skF_2'(A_46, B_47), '#skF_4') | ~r1_tarski(B_47, '#skF_6') | r1_xboole_0(A_46, B_47))), inference(resolution, [status(thm)], [c_119, c_44])).
% 2.07/1.22  tff(c_219, plain, (![B_52, A_53]: (~r1_tarski(B_52, '#skF_6') | ~r1_tarski(A_53, '#skF_4') | r1_xboole_0(A_53, B_52))), inference(resolution, [status(thm)], [c_39, c_180])).
% 2.07/1.22  tff(c_14, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.07/1.22  tff(c_224, plain, (~r1_tarski('#skF_5', '#skF_6') | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_219, c_14])).
% 2.07/1.22  tff(c_229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_224])).
% 2.07/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.22  
% 2.07/1.22  Inference rules
% 2.07/1.22  ----------------------
% 2.07/1.22  #Ref     : 0
% 2.07/1.22  #Sup     : 44
% 2.07/1.22  #Fact    : 0
% 2.07/1.22  #Define  : 0
% 2.07/1.22  #Split   : 3
% 2.07/1.22  #Chain   : 0
% 2.07/1.22  #Close   : 0
% 2.07/1.22  
% 2.07/1.22  Ordering : KBO
% 2.07/1.22  
% 2.07/1.22  Simplification rules
% 2.07/1.22  ----------------------
% 2.07/1.22  #Subsume      : 6
% 2.07/1.22  #Demod        : 4
% 2.07/1.22  #Tautology    : 2
% 2.07/1.22  #SimpNegUnit  : 0
% 2.07/1.22  #BackRed      : 0
% 2.07/1.22  
% 2.07/1.22  #Partial instantiations: 0
% 2.07/1.22  #Strategies tried      : 1
% 2.07/1.22  
% 2.07/1.22  Timing (in seconds)
% 2.07/1.22  ----------------------
% 2.07/1.23  Preprocessing        : 0.26
% 2.07/1.23  Parsing              : 0.14
% 2.07/1.23  CNF conversion       : 0.02
% 2.07/1.23  Main loop            : 0.21
% 2.07/1.23  Inferencing          : 0.09
% 2.07/1.23  Reduction            : 0.05
% 2.10/1.23  Demodulation         : 0.03
% 2.10/1.23  BG Simplification    : 0.01
% 2.10/1.23  Subsumption          : 0.05
% 2.10/1.23  Abstraction          : 0.01
% 2.10/1.23  MUC search           : 0.00
% 2.10/1.23  Cooper               : 0.00
% 2.10/1.23  Total                : 0.49
% 2.10/1.23  Index Insertion      : 0.00
% 2.10/1.23  Index Deletion       : 0.00
% 2.10/1.23  Index Matching       : 0.00
% 2.10/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
