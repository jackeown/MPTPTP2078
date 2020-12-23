%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:15 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  59 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > #nlpp > k1_setfam_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r1_xboole_0(A,C) )
       => r1_xboole_0(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_setfam_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

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
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_setfam_1(B_12),A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_69,plain,(
    ! [C_31,B_32,A_33] :
      ( r2_hidden(C_31,B_32)
      | ~ r2_hidden(C_31,A_33)
      | ~ r1_tarski(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_139,plain,(
    ! [A_45,B_46,B_47] :
      ( r2_hidden('#skF_2'(A_45,B_46),B_47)
      | ~ r1_tarski(A_45,B_47)
      | r1_xboole_0(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_12,c_69])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [A_24,B_25,C_26] :
      ( ~ r1_xboole_0(A_24,B_25)
      | ~ r2_hidden(C_26,B_25)
      | ~ r2_hidden(C_26,A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    ! [C_27] :
      ( ~ r2_hidden(C_27,'#skF_5')
      | ~ r2_hidden(C_27,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_32])).

tff(c_50,plain,(
    ! [A_6] :
      ( ~ r2_hidden('#skF_2'(A_6,'#skF_5'),'#skF_3')
      | r1_xboole_0(A_6,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10,c_36])).

tff(c_162,plain,(
    ! [A_49] :
      ( ~ r1_tarski(A_49,'#skF_3')
      | r1_xboole_0(A_49,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_139,c_50])).

tff(c_16,plain,(
    ~ r1_xboole_0(k1_setfam_1('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_169,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_162,c_16])).

tff(c_172,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_169])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:58:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.18  
% 1.90/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.18  %$ r2_hidden > r1_xboole_0 > r1_tarski > #nlpp > k1_setfam_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.90/1.18  
% 1.90/1.18  %Foreground sorts:
% 1.90/1.18  
% 1.90/1.18  
% 1.90/1.18  %Background operators:
% 1.90/1.18  
% 1.90/1.18  
% 1.90/1.18  %Foreground operators:
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.90/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.90/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.90/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.90/1.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.90/1.18  
% 1.90/1.19  tff(f_61, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r1_xboole_0(A, C)) => r1_xboole_0(k1_setfam_1(B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_setfam_1)).
% 1.90/1.19  tff(f_54, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.90/1.19  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.90/1.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.90/1.19  tff(c_20, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.90/1.19  tff(c_14, plain, (![B_12, A_11]: (r1_tarski(k1_setfam_1(B_12), A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.90/1.19  tff(c_12, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.90/1.19  tff(c_69, plain, (![C_31, B_32, A_33]: (r2_hidden(C_31, B_32) | ~r2_hidden(C_31, A_33) | ~r1_tarski(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.90/1.19  tff(c_139, plain, (![A_45, B_46, B_47]: (r2_hidden('#skF_2'(A_45, B_46), B_47) | ~r1_tarski(A_45, B_47) | r1_xboole_0(A_45, B_46))), inference(resolution, [status(thm)], [c_12, c_69])).
% 1.90/1.19  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.90/1.19  tff(c_18, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.90/1.19  tff(c_32, plain, (![A_24, B_25, C_26]: (~r1_xboole_0(A_24, B_25) | ~r2_hidden(C_26, B_25) | ~r2_hidden(C_26, A_24))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.90/1.19  tff(c_36, plain, (![C_27]: (~r2_hidden(C_27, '#skF_5') | ~r2_hidden(C_27, '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_32])).
% 1.90/1.19  tff(c_50, plain, (![A_6]: (~r2_hidden('#skF_2'(A_6, '#skF_5'), '#skF_3') | r1_xboole_0(A_6, '#skF_5'))), inference(resolution, [status(thm)], [c_10, c_36])).
% 1.90/1.19  tff(c_162, plain, (![A_49]: (~r1_tarski(A_49, '#skF_3') | r1_xboole_0(A_49, '#skF_5'))), inference(resolution, [status(thm)], [c_139, c_50])).
% 1.90/1.19  tff(c_16, plain, (~r1_xboole_0(k1_setfam_1('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.90/1.19  tff(c_169, plain, (~r1_tarski(k1_setfam_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_162, c_16])).
% 1.90/1.19  tff(c_172, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_14, c_169])).
% 1.90/1.19  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_172])).
% 1.90/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.19  
% 1.90/1.19  Inference rules
% 1.90/1.19  ----------------------
% 1.90/1.19  #Ref     : 0
% 1.90/1.19  #Sup     : 32
% 1.90/1.19  #Fact    : 0
% 1.90/1.19  #Define  : 0
% 1.90/1.19  #Split   : 2
% 1.90/1.19  #Chain   : 0
% 1.90/1.19  #Close   : 0
% 1.90/1.19  
% 1.90/1.19  Ordering : KBO
% 1.90/1.19  
% 1.90/1.19  Simplification rules
% 1.90/1.19  ----------------------
% 1.90/1.19  #Subsume      : 4
% 1.90/1.19  #Demod        : 2
% 1.90/1.19  #Tautology    : 2
% 1.90/1.19  #SimpNegUnit  : 0
% 1.90/1.19  #BackRed      : 0
% 1.90/1.19  
% 1.90/1.19  #Partial instantiations: 0
% 1.90/1.19  #Strategies tried      : 1
% 1.90/1.19  
% 1.90/1.19  Timing (in seconds)
% 1.90/1.19  ----------------------
% 1.90/1.20  Preprocessing        : 0.25
% 1.90/1.20  Parsing              : 0.14
% 1.90/1.20  CNF conversion       : 0.02
% 1.90/1.20  Main loop            : 0.18
% 1.90/1.20  Inferencing          : 0.08
% 1.90/1.20  Reduction            : 0.04
% 1.90/1.20  Demodulation         : 0.03
% 1.90/1.20  BG Simplification    : 0.01
% 1.90/1.20  Subsumption          : 0.04
% 1.90/1.20  Abstraction          : 0.01
% 1.90/1.20  MUC search           : 0.00
% 1.90/1.20  Cooper               : 0.00
% 1.90/1.20  Total                : 0.46
% 1.90/1.20  Index Insertion      : 0.00
% 1.90/1.20  Index Deletion       : 0.00
% 1.90/1.20  Index Matching       : 0.00
% 1.90/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
