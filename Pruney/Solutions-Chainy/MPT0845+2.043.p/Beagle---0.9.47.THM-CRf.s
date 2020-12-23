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
% DateTime   : Thu Dec  3 10:08:50 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 (  65 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_52,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

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

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_124,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_1'(A_49,B_50),B_50)
      | r2_hidden('#skF_2'(A_49,B_50),A_49)
      | B_50 = A_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( ~ r1_tarski(B_18,A_17)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_279,plain,(
    ! [B_63,A_64] :
      ( ~ r1_tarski(B_63,'#skF_1'(A_64,B_63))
      | r2_hidden('#skF_2'(A_64,B_63),A_64)
      | B_63 = A_64 ) ),
    inference(resolution,[status(thm)],[c_124,c_22])).

tff(c_283,plain,(
    ! [A_64] :
      ( r2_hidden('#skF_2'(A_64,k1_xboole_0),A_64)
      | k1_xboole_0 = A_64 ) ),
    inference(resolution,[status(thm)],[c_16,c_279])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_3'(A_4,B_5),B_5)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_3'(A_4,B_5),A_4)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_108,plain,(
    ! [D_46,A_47,B_48] :
      ( ~ r2_hidden(D_46,'#skF_4'(A_47,B_48))
      | ~ r2_hidden(D_46,B_48)
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_336,plain,(
    ! [A_79,B_80,B_81] :
      ( ~ r2_hidden('#skF_3'('#skF_4'(A_79,B_80),B_81),B_80)
      | ~ r2_hidden(A_79,B_80)
      | r1_xboole_0('#skF_4'(A_79,B_80),B_81) ) ),
    inference(resolution,[status(thm)],[c_14,c_108])).

tff(c_342,plain,(
    ! [A_82,B_83] :
      ( ~ r2_hidden(A_82,B_83)
      | r1_xboole_0('#skF_4'(A_82,B_83),B_83) ) ),
    inference(resolution,[status(thm)],[c_12,c_336])).

tff(c_30,plain,(
    ! [A_25,B_26] :
      ( r2_hidden('#skF_4'(A_25,B_26),B_26)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24,plain,(
    ! [B_20] :
      ( ~ r1_xboole_0(B_20,'#skF_5')
      | ~ r2_hidden(B_20,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_39,plain,(
    ! [A_25] :
      ( ~ r1_xboole_0('#skF_4'(A_25,'#skF_5'),'#skF_5')
      | ~ r2_hidden(A_25,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_24])).

tff(c_351,plain,(
    ! [A_84] : ~ r2_hidden(A_84,'#skF_5') ),
    inference(resolution,[status(thm)],[c_342,c_39])).

tff(c_355,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_283,c_351])).

tff(c_389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_355])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:54:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.27  
% 2.28/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.27  %$ r2_hidden > r1_xboole_0 > r1_tarski > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 2.28/1.27  
% 2.28/1.27  %Foreground sorts:
% 2.28/1.27  
% 2.28/1.27  
% 2.28/1.27  %Background operators:
% 2.28/1.27  
% 2.28/1.27  
% 2.28/1.27  %Foreground operators:
% 2.28/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.28/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.28/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.28/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.28/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.28/1.27  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.28/1.27  
% 2.28/1.28  tff(f_81, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.28/1.28  tff(f_52, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.28/1.28  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 2.28/1.28  tff(f_70, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.28/1.28  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.28/1.28  tff(f_65, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 2.28/1.28  tff(c_26, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.28/1.28  tff(c_16, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.28/1.28  tff(c_124, plain, (![A_49, B_50]: (r2_hidden('#skF_1'(A_49, B_50), B_50) | r2_hidden('#skF_2'(A_49, B_50), A_49) | B_50=A_49)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.28/1.28  tff(c_22, plain, (![B_18, A_17]: (~r1_tarski(B_18, A_17) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.28/1.28  tff(c_279, plain, (![B_63, A_64]: (~r1_tarski(B_63, '#skF_1'(A_64, B_63)) | r2_hidden('#skF_2'(A_64, B_63), A_64) | B_63=A_64)), inference(resolution, [status(thm)], [c_124, c_22])).
% 2.28/1.28  tff(c_283, plain, (![A_64]: (r2_hidden('#skF_2'(A_64, k1_xboole_0), A_64) | k1_xboole_0=A_64)), inference(resolution, [status(thm)], [c_16, c_279])).
% 2.28/1.28  tff(c_12, plain, (![A_4, B_5]: (r2_hidden('#skF_3'(A_4, B_5), B_5) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.28  tff(c_14, plain, (![A_4, B_5]: (r2_hidden('#skF_3'(A_4, B_5), A_4) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.28  tff(c_108, plain, (![D_46, A_47, B_48]: (~r2_hidden(D_46, '#skF_4'(A_47, B_48)) | ~r2_hidden(D_46, B_48) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.28/1.28  tff(c_336, plain, (![A_79, B_80, B_81]: (~r2_hidden('#skF_3'('#skF_4'(A_79, B_80), B_81), B_80) | ~r2_hidden(A_79, B_80) | r1_xboole_0('#skF_4'(A_79, B_80), B_81))), inference(resolution, [status(thm)], [c_14, c_108])).
% 2.28/1.28  tff(c_342, plain, (![A_82, B_83]: (~r2_hidden(A_82, B_83) | r1_xboole_0('#skF_4'(A_82, B_83), B_83))), inference(resolution, [status(thm)], [c_12, c_336])).
% 2.28/1.28  tff(c_30, plain, (![A_25, B_26]: (r2_hidden('#skF_4'(A_25, B_26), B_26) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.28/1.28  tff(c_24, plain, (![B_20]: (~r1_xboole_0(B_20, '#skF_5') | ~r2_hidden(B_20, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.28/1.28  tff(c_39, plain, (![A_25]: (~r1_xboole_0('#skF_4'(A_25, '#skF_5'), '#skF_5') | ~r2_hidden(A_25, '#skF_5'))), inference(resolution, [status(thm)], [c_30, c_24])).
% 2.28/1.28  tff(c_351, plain, (![A_84]: (~r2_hidden(A_84, '#skF_5'))), inference(resolution, [status(thm)], [c_342, c_39])).
% 2.28/1.28  tff(c_355, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_283, c_351])).
% 2.28/1.28  tff(c_389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_355])).
% 2.28/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.28  
% 2.28/1.28  Inference rules
% 2.28/1.28  ----------------------
% 2.28/1.28  #Ref     : 0
% 2.28/1.28  #Sup     : 63
% 2.28/1.28  #Fact    : 0
% 2.28/1.28  #Define  : 0
% 2.28/1.28  #Split   : 0
% 2.28/1.28  #Chain   : 0
% 2.28/1.28  #Close   : 0
% 2.28/1.28  
% 2.28/1.28  Ordering : KBO
% 2.28/1.28  
% 2.28/1.28  Simplification rules
% 2.28/1.28  ----------------------
% 2.28/1.28  #Subsume      : 13
% 2.28/1.28  #Demod        : 3
% 2.28/1.28  #Tautology    : 13
% 2.28/1.28  #SimpNegUnit  : 6
% 2.28/1.28  #BackRed      : 0
% 2.28/1.28  
% 2.28/1.28  #Partial instantiations: 0
% 2.28/1.28  #Strategies tried      : 1
% 2.28/1.28  
% 2.28/1.28  Timing (in seconds)
% 2.28/1.28  ----------------------
% 2.28/1.29  Preprocessing        : 0.29
% 2.28/1.29  Parsing              : 0.15
% 2.28/1.29  CNF conversion       : 0.02
% 2.28/1.29  Main loop            : 0.24
% 2.28/1.29  Inferencing          : 0.11
% 2.28/1.29  Reduction            : 0.06
% 2.28/1.29  Demodulation         : 0.04
% 2.28/1.29  BG Simplification    : 0.02
% 2.28/1.29  Subsumption          : 0.04
% 2.28/1.29  Abstraction          : 0.01
% 2.28/1.29  MUC search           : 0.00
% 2.28/1.29  Cooper               : 0.00
% 2.28/1.29  Total                : 0.55
% 2.28/1.29  Index Insertion      : 0.00
% 2.28/1.29  Index Deletion       : 0.00
% 2.28/1.29  Index Matching       : 0.00
% 2.28/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
