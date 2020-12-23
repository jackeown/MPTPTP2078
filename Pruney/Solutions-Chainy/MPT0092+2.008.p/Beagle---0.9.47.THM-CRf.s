%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:29 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  56 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_54,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_20,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),B_9)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_41,plain,(
    ! [C_30,B_31,A_32] :
      ( r2_hidden(C_30,B_31)
      | ~ r2_hidden(C_30,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    ! [A_8,B_9,B_31] :
      ( r2_hidden('#skF_2'(A_8,B_9),B_31)
      | ~ r1_tarski(B_9,B_31)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_41])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),A_8)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_51,plain,(
    ! [A_33,B_34,C_35] :
      ( ~ r1_xboole_0(A_33,B_34)
      | ~ r2_hidden(C_35,B_34)
      | ~ r2_hidden(C_35,A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_58,plain,(
    ! [C_36,B_37,A_38] :
      ( ~ r2_hidden(C_36,B_37)
      | ~ r2_hidden(C_36,k4_xboole_0(A_38,B_37)) ) ),
    inference(resolution,[status(thm)],[c_16,c_51])).

tff(c_129,plain,(
    ! [A_57,B_58,B_59] :
      ( ~ r2_hidden('#skF_2'(k4_xboole_0(A_57,B_58),B_59),B_58)
      | r1_xboole_0(k4_xboole_0(A_57,B_58),B_59) ) ),
    inference(resolution,[status(thm)],[c_14,c_58])).

tff(c_146,plain,(
    ! [B_60,B_61,A_62] :
      ( ~ r1_tarski(B_60,B_61)
      | r1_xboole_0(k4_xboole_0(A_62,B_61),B_60) ) ),
    inference(resolution,[status(thm)],[c_48,c_129])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_xboole_0(B_7,A_6)
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_153,plain,(
    ! [B_63,A_64,B_65] :
      ( r1_xboole_0(B_63,k4_xboole_0(A_64,B_65))
      | ~ r1_tarski(B_63,B_65) ) ),
    inference(resolution,[status(thm)],[c_146,c_8])).

tff(c_18,plain,(
    ~ r1_xboole_0('#skF_3',k4_xboole_0('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_160,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_153,c_18])).

tff(c_166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.16  
% 1.63/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.17  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.63/1.17  
% 1.63/1.17  %Foreground sorts:
% 1.63/1.17  
% 1.63/1.17  
% 1.63/1.17  %Background operators:
% 1.63/1.17  
% 1.63/1.17  
% 1.63/1.17  %Foreground operators:
% 1.63/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.63/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.63/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.63/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.63/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.63/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.63/1.17  
% 1.95/1.18  tff(f_61, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.95/1.18  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.95/1.18  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.95/1.18  tff(f_56, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.95/1.18  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.95/1.18  tff(c_20, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.95/1.18  tff(c_12, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), B_9) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.95/1.18  tff(c_41, plain, (![C_30, B_31, A_32]: (r2_hidden(C_30, B_31) | ~r2_hidden(C_30, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.95/1.18  tff(c_48, plain, (![A_8, B_9, B_31]: (r2_hidden('#skF_2'(A_8, B_9), B_31) | ~r1_tarski(B_9, B_31) | r1_xboole_0(A_8, B_9))), inference(resolution, [status(thm)], [c_12, c_41])).
% 1.95/1.18  tff(c_14, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), A_8) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.95/1.18  tff(c_16, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.95/1.18  tff(c_51, plain, (![A_33, B_34, C_35]: (~r1_xboole_0(A_33, B_34) | ~r2_hidden(C_35, B_34) | ~r2_hidden(C_35, A_33))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.95/1.18  tff(c_58, plain, (![C_36, B_37, A_38]: (~r2_hidden(C_36, B_37) | ~r2_hidden(C_36, k4_xboole_0(A_38, B_37)))), inference(resolution, [status(thm)], [c_16, c_51])).
% 1.95/1.18  tff(c_129, plain, (![A_57, B_58, B_59]: (~r2_hidden('#skF_2'(k4_xboole_0(A_57, B_58), B_59), B_58) | r1_xboole_0(k4_xboole_0(A_57, B_58), B_59))), inference(resolution, [status(thm)], [c_14, c_58])).
% 1.95/1.18  tff(c_146, plain, (![B_60, B_61, A_62]: (~r1_tarski(B_60, B_61) | r1_xboole_0(k4_xboole_0(A_62, B_61), B_60))), inference(resolution, [status(thm)], [c_48, c_129])).
% 1.95/1.18  tff(c_8, plain, (![B_7, A_6]: (r1_xboole_0(B_7, A_6) | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.95/1.18  tff(c_153, plain, (![B_63, A_64, B_65]: (r1_xboole_0(B_63, k4_xboole_0(A_64, B_65)) | ~r1_tarski(B_63, B_65))), inference(resolution, [status(thm)], [c_146, c_8])).
% 1.95/1.18  tff(c_18, plain, (~r1_xboole_0('#skF_3', k4_xboole_0('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.95/1.18  tff(c_160, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_153, c_18])).
% 1.95/1.18  tff(c_166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_160])).
% 1.95/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.18  
% 1.95/1.18  Inference rules
% 1.95/1.18  ----------------------
% 1.95/1.18  #Ref     : 0
% 1.95/1.18  #Sup     : 30
% 1.95/1.18  #Fact    : 0
% 1.95/1.18  #Define  : 0
% 1.95/1.18  #Split   : 0
% 1.95/1.18  #Chain   : 0
% 1.95/1.18  #Close   : 0
% 1.95/1.18  
% 1.95/1.18  Ordering : KBO
% 1.95/1.18  
% 1.95/1.18  Simplification rules
% 1.95/1.18  ----------------------
% 1.95/1.18  #Subsume      : 2
% 1.95/1.18  #Demod        : 3
% 1.95/1.18  #Tautology    : 3
% 1.95/1.18  #SimpNegUnit  : 0
% 1.95/1.18  #BackRed      : 0
% 1.95/1.18  
% 1.95/1.18  #Partial instantiations: 0
% 1.95/1.18  #Strategies tried      : 1
% 1.95/1.18  
% 1.95/1.18  Timing (in seconds)
% 1.95/1.18  ----------------------
% 1.95/1.18  Preprocessing        : 0.26
% 1.95/1.18  Parsing              : 0.15
% 1.95/1.18  CNF conversion       : 0.02
% 1.95/1.18  Main loop            : 0.16
% 1.95/1.18  Inferencing          : 0.07
% 1.95/1.19  Reduction            : 0.04
% 1.95/1.19  Demodulation         : 0.03
% 1.95/1.19  BG Simplification    : 0.01
% 1.95/1.19  Subsumption          : 0.03
% 1.95/1.19  Abstraction          : 0.01
% 1.95/1.19  MUC search           : 0.00
% 1.95/1.19  Cooper               : 0.00
% 1.95/1.19  Total                : 0.45
% 1.95/1.19  Index Insertion      : 0.00
% 1.95/1.19  Index Deletion       : 0.00
% 1.95/1.19  Index Matching       : 0.00
% 1.95/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
