%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:45 EST 2020

% Result     : Theorem 14.43s
% Output     : CNFRefutation 14.43s
% Verified   : 
% Statistics : Number of formulae       :   28 (  32 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  46 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_xboole_0 > k4_xboole_0 > #nlpp > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

tff(c_42,plain,(
    ! [A_23,B_24] :
      ( r2_hidden('#skF_1'(A_23,B_24),A_23)
      | r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_56,plain,(
    ! [A_6,B_7,B_24] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_6,B_7),B_24),A_6)
      | r1_tarski(k4_xboole_0(A_6,B_7),B_24) ) ),
    inference(resolution,[status(thm)],[c_42,c_12])).

tff(c_99,plain,(
    ! [A_38,C_39,B_40] :
      ( r2_hidden(A_38,C_39)
      | ~ r2_hidden(A_38,B_40)
      | r2_hidden(A_38,k5_xboole_0(B_40,C_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3771,plain,(
    ! [A_250,B_251,C_252] :
      ( r1_tarski(A_250,k5_xboole_0(B_251,C_252))
      | r2_hidden('#skF_1'(A_250,k5_xboole_0(B_251,C_252)),C_252)
      | ~ r2_hidden('#skF_1'(A_250,k5_xboole_0(B_251,C_252)),B_251) ) ),
    inference(resolution,[status(thm)],[c_99,c_4])).

tff(c_34375,plain,(
    ! [A_740,B_741,C_742] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_740,B_741),k5_xboole_0(A_740,C_742)),C_742)
      | r1_tarski(k4_xboole_0(A_740,B_741),k5_xboole_0(A_740,C_742)) ) ),
    inference(resolution,[status(thm)],[c_56,c_3771])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_55,plain,(
    ! [A_6,B_7,B_24] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_6,B_7),B_24),B_7)
      | r1_tarski(k4_xboole_0(A_6,B_7),B_24) ) ),
    inference(resolution,[status(thm)],[c_42,c_10])).

tff(c_34573,plain,(
    ! [A_740,C_742] : r1_tarski(k4_xboole_0(A_740,C_742),k5_xboole_0(A_740,C_742)) ),
    inference(resolution,[status(thm)],[c_34375,c_55])).

tff(c_38,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_4','#skF_5'),k5_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34573,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.43/6.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.43/6.14  
% 14.43/6.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.43/6.15  %$ r2_hidden > r1_tarski > k5_xboole_0 > k4_xboole_0 > #nlpp > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 14.43/6.15  
% 14.43/6.15  %Foreground sorts:
% 14.43/6.15  
% 14.43/6.15  
% 14.43/6.15  %Background operators:
% 14.43/6.15  
% 14.43/6.15  
% 14.43/6.15  %Foreground operators:
% 14.43/6.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.43/6.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.43/6.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.43/6.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.43/6.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.43/6.15  tff('#skF_5', type, '#skF_5': $i).
% 14.43/6.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.43/6.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.43/6.15  tff('#skF_4', type, '#skF_4': $i).
% 14.43/6.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.43/6.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.43/6.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.43/6.15  
% 14.43/6.16  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 14.43/6.16  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 14.43/6.16  tff(f_49, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 14.43/6.16  tff(f_52, negated_conjecture, ~(![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_xboole_1)).
% 14.43/6.16  tff(c_42, plain, (![A_23, B_24]: (r2_hidden('#skF_1'(A_23, B_24), A_23) | r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.43/6.16  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.43/6.16  tff(c_56, plain, (![A_6, B_7, B_24]: (r2_hidden('#skF_1'(k4_xboole_0(A_6, B_7), B_24), A_6) | r1_tarski(k4_xboole_0(A_6, B_7), B_24))), inference(resolution, [status(thm)], [c_42, c_12])).
% 14.43/6.16  tff(c_99, plain, (![A_38, C_39, B_40]: (r2_hidden(A_38, C_39) | ~r2_hidden(A_38, B_40) | r2_hidden(A_38, k5_xboole_0(B_40, C_39)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.43/6.16  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.43/6.16  tff(c_3771, plain, (![A_250, B_251, C_252]: (r1_tarski(A_250, k5_xboole_0(B_251, C_252)) | r2_hidden('#skF_1'(A_250, k5_xboole_0(B_251, C_252)), C_252) | ~r2_hidden('#skF_1'(A_250, k5_xboole_0(B_251, C_252)), B_251))), inference(resolution, [status(thm)], [c_99, c_4])).
% 14.43/6.16  tff(c_34375, plain, (![A_740, B_741, C_742]: (r2_hidden('#skF_1'(k4_xboole_0(A_740, B_741), k5_xboole_0(A_740, C_742)), C_742) | r1_tarski(k4_xboole_0(A_740, B_741), k5_xboole_0(A_740, C_742)))), inference(resolution, [status(thm)], [c_56, c_3771])).
% 14.43/6.16  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.43/6.16  tff(c_55, plain, (![A_6, B_7, B_24]: (~r2_hidden('#skF_1'(k4_xboole_0(A_6, B_7), B_24), B_7) | r1_tarski(k4_xboole_0(A_6, B_7), B_24))), inference(resolution, [status(thm)], [c_42, c_10])).
% 14.43/6.16  tff(c_34573, plain, (![A_740, C_742]: (r1_tarski(k4_xboole_0(A_740, C_742), k5_xboole_0(A_740, C_742)))), inference(resolution, [status(thm)], [c_34375, c_55])).
% 14.43/6.16  tff(c_38, plain, (~r1_tarski(k4_xboole_0('#skF_4', '#skF_5'), k5_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 14.43/6.16  tff(c_34603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34573, c_38])).
% 14.43/6.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.43/6.16  
% 14.43/6.16  Inference rules
% 14.43/6.16  ----------------------
% 14.43/6.16  #Ref     : 0
% 14.43/6.16  #Sup     : 9266
% 14.43/6.16  #Fact    : 8
% 14.43/6.16  #Define  : 0
% 14.43/6.16  #Split   : 0
% 14.43/6.16  #Chain   : 0
% 14.43/6.16  #Close   : 0
% 14.43/6.16  
% 14.43/6.16  Ordering : KBO
% 14.43/6.16  
% 14.43/6.16  Simplification rules
% 14.43/6.16  ----------------------
% 14.43/6.16  #Subsume      : 2203
% 14.43/6.16  #Demod        : 4267
% 14.43/6.16  #Tautology    : 3018
% 14.43/6.16  #SimpNegUnit  : 0
% 14.43/6.16  #BackRed      : 6
% 14.43/6.16  
% 14.43/6.16  #Partial instantiations: 0
% 14.43/6.16  #Strategies tried      : 1
% 14.43/6.16  
% 14.43/6.16  Timing (in seconds)
% 14.43/6.16  ----------------------
% 14.43/6.17  Preprocessing        : 0.27
% 14.43/6.17  Parsing              : 0.14
% 14.43/6.17  CNF conversion       : 0.02
% 14.43/6.17  Main loop            : 5.12
% 14.43/6.17  Inferencing          : 1.01
% 14.43/6.17  Reduction            : 1.96
% 14.43/6.17  Demodulation         : 1.66
% 14.43/6.17  BG Simplification    : 0.13
% 14.43/6.17  Subsumption          : 1.71
% 14.43/6.17  Abstraction          : 0.19
% 14.43/6.17  MUC search           : 0.00
% 14.43/6.17  Cooper               : 0.00
% 14.43/6.17  Total                : 5.43
% 14.43/6.17  Index Insertion      : 0.00
% 14.43/6.17  Index Deletion       : 0.00
% 14.43/6.17  Index Matching       : 0.00
% 14.43/6.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
