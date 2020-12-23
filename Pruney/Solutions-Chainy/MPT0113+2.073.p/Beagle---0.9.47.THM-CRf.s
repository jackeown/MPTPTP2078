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
% DateTime   : Thu Dec  3 09:45:20 EST 2020

% Result     : Theorem 11.69s
% Output     : CNFRefutation 11.91s
% Verified   : 
% Statistics : Number of formulae       :   40 (  53 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 (  96 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

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

tff(f_60,axiom,(
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

tff(c_32,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_7')
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_35,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_34,plain,(
    r1_tarski('#skF_5',k4_xboole_0('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    ! [C_32,B_33,A_34] :
      ( r2_hidden(C_32,B_33)
      | ~ r2_hidden(C_32,A_34)
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_139,plain,(
    ! [A_50,B_51,B_52] :
      ( r2_hidden('#skF_1'(A_50,B_51),B_52)
      | ~ r1_tarski(A_50,B_52)
      | r1_tarski(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_6,c_78])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12638,plain,(
    ! [A_573,B_574,A_575,B_576] :
      ( r2_hidden('#skF_1'(A_573,B_574),A_575)
      | ~ r1_tarski(A_573,k4_xboole_0(A_575,B_576))
      | r1_tarski(A_573,B_574) ) ),
    inference(resolution,[status(thm)],[c_139,c_12])).

tff(c_12701,plain,(
    ! [B_577] :
      ( r2_hidden('#skF_1'('#skF_5',B_577),'#skF_6')
      | r1_tarski('#skF_5',B_577) ) ),
    inference(resolution,[status(thm)],[c_34,c_12638])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12714,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_12701,c_4])).

tff(c_12722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_35,c_12714])).

tff(c_12723,plain,(
    ~ r1_xboole_0('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_4'(A_12,B_13),B_13)
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_4'(A_12,B_13),A_12)
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12768,plain,(
    ! [C_596,B_597,A_598] :
      ( r2_hidden(C_596,B_597)
      | ~ r2_hidden(C_596,A_598)
      | ~ r1_tarski(A_598,B_597) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12815,plain,(
    ! [A_608,B_609,B_610] :
      ( r2_hidden('#skF_4'(A_608,B_609),B_610)
      | ~ r1_tarski(A_608,B_610)
      | r1_xboole_0(A_608,B_609) ) ),
    inference(resolution,[status(thm)],[c_30,c_12768])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_23869,plain,(
    ! [A_1039,B_1040,B_1041,A_1042] :
      ( ~ r2_hidden('#skF_4'(A_1039,B_1040),B_1041)
      | ~ r1_tarski(A_1039,k4_xboole_0(A_1042,B_1041))
      | r1_xboole_0(A_1039,B_1040) ) ),
    inference(resolution,[status(thm)],[c_12815,c_10])).

tff(c_23957,plain,(
    ! [A_1046,A_1047,B_1048] :
      ( ~ r1_tarski(A_1046,k4_xboole_0(A_1047,B_1048))
      | r1_xboole_0(A_1046,B_1048) ) ),
    inference(resolution,[status(thm)],[c_28,c_23869])).

tff(c_24024,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_23957])).

tff(c_24045,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12723,c_24024])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:11:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.69/4.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.69/4.55  
% 11.69/4.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.69/4.55  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.69/4.55  
% 11.69/4.55  %Foreground sorts:
% 11.69/4.55  
% 11.69/4.55  
% 11.69/4.55  %Background operators:
% 11.69/4.55  
% 11.69/4.55  
% 11.69/4.55  %Foreground operators:
% 11.69/4.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.69/4.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.69/4.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.69/4.55  tff('#skF_7', type, '#skF_7': $i).
% 11.69/4.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.69/4.55  tff('#skF_5', type, '#skF_5': $i).
% 11.69/4.55  tff('#skF_6', type, '#skF_6': $i).
% 11.69/4.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.69/4.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.69/4.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.69/4.55  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.69/4.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.69/4.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.69/4.55  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.69/4.55  
% 11.91/4.56  tff(f_67, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 11.91/4.56  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.91/4.56  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 11.91/4.56  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 11.91/4.56  tff(c_32, plain, (~r1_xboole_0('#skF_5', '#skF_7') | ~r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.91/4.56  tff(c_35, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_32])).
% 11.91/4.56  tff(c_34, plain, (r1_tarski('#skF_5', k4_xboole_0('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.91/4.56  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.91/4.56  tff(c_78, plain, (![C_32, B_33, A_34]: (r2_hidden(C_32, B_33) | ~r2_hidden(C_32, A_34) | ~r1_tarski(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.91/4.56  tff(c_139, plain, (![A_50, B_51, B_52]: (r2_hidden('#skF_1'(A_50, B_51), B_52) | ~r1_tarski(A_50, B_52) | r1_tarski(A_50, B_51))), inference(resolution, [status(thm)], [c_6, c_78])).
% 11.91/4.56  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.91/4.56  tff(c_12638, plain, (![A_573, B_574, A_575, B_576]: (r2_hidden('#skF_1'(A_573, B_574), A_575) | ~r1_tarski(A_573, k4_xboole_0(A_575, B_576)) | r1_tarski(A_573, B_574))), inference(resolution, [status(thm)], [c_139, c_12])).
% 11.91/4.56  tff(c_12701, plain, (![B_577]: (r2_hidden('#skF_1'('#skF_5', B_577), '#skF_6') | r1_tarski('#skF_5', B_577))), inference(resolution, [status(thm)], [c_34, c_12638])).
% 11.91/4.56  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.91/4.56  tff(c_12714, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_12701, c_4])).
% 11.91/4.56  tff(c_12722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_35, c_12714])).
% 11.91/4.56  tff(c_12723, plain, (~r1_xboole_0('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_32])).
% 11.91/4.56  tff(c_28, plain, (![A_12, B_13]: (r2_hidden('#skF_4'(A_12, B_13), B_13) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.91/4.56  tff(c_30, plain, (![A_12, B_13]: (r2_hidden('#skF_4'(A_12, B_13), A_12) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.91/4.56  tff(c_12768, plain, (![C_596, B_597, A_598]: (r2_hidden(C_596, B_597) | ~r2_hidden(C_596, A_598) | ~r1_tarski(A_598, B_597))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.91/4.56  tff(c_12815, plain, (![A_608, B_609, B_610]: (r2_hidden('#skF_4'(A_608, B_609), B_610) | ~r1_tarski(A_608, B_610) | r1_xboole_0(A_608, B_609))), inference(resolution, [status(thm)], [c_30, c_12768])).
% 11.91/4.56  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.91/4.56  tff(c_23869, plain, (![A_1039, B_1040, B_1041, A_1042]: (~r2_hidden('#skF_4'(A_1039, B_1040), B_1041) | ~r1_tarski(A_1039, k4_xboole_0(A_1042, B_1041)) | r1_xboole_0(A_1039, B_1040))), inference(resolution, [status(thm)], [c_12815, c_10])).
% 11.91/4.56  tff(c_23957, plain, (![A_1046, A_1047, B_1048]: (~r1_tarski(A_1046, k4_xboole_0(A_1047, B_1048)) | r1_xboole_0(A_1046, B_1048))), inference(resolution, [status(thm)], [c_28, c_23869])).
% 11.91/4.56  tff(c_24024, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_34, c_23957])).
% 11.91/4.56  tff(c_24045, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12723, c_24024])).
% 11.91/4.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.91/4.56  
% 11.91/4.56  Inference rules
% 11.91/4.56  ----------------------
% 11.91/4.56  #Ref     : 0
% 11.91/4.56  #Sup     : 6620
% 11.91/4.56  #Fact    : 0
% 11.91/4.56  #Define  : 0
% 11.91/4.56  #Split   : 22
% 11.91/4.56  #Chain   : 0
% 11.91/4.56  #Close   : 0
% 11.91/4.56  
% 11.91/4.56  Ordering : KBO
% 11.91/4.56  
% 11.91/4.56  Simplification rules
% 11.91/4.56  ----------------------
% 11.91/4.56  #Subsume      : 2395
% 11.91/4.56  #Demod        : 2765
% 11.91/4.56  #Tautology    : 1848
% 11.91/4.56  #SimpNegUnit  : 10
% 11.91/4.56  #BackRed      : 10
% 11.91/4.56  
% 11.91/4.56  #Partial instantiations: 0
% 11.91/4.56  #Strategies tried      : 1
% 11.91/4.56  
% 11.91/4.56  Timing (in seconds)
% 11.91/4.56  ----------------------
% 11.91/4.57  Preprocessing        : 0.40
% 11.91/4.57  Parsing              : 0.22
% 11.91/4.57  CNF conversion       : 0.03
% 11.91/4.57  Main loop            : 3.25
% 11.91/4.57  Inferencing          : 0.81
% 11.91/4.57  Reduction            : 1.08
% 11.91/4.57  Demodulation         : 0.85
% 11.91/4.57  BG Simplification    : 0.09
% 11.91/4.57  Subsumption          : 1.05
% 11.91/4.57  Abstraction          : 0.14
% 11.91/4.57  MUC search           : 0.00
% 11.91/4.57  Cooper               : 0.00
% 11.91/4.57  Total                : 3.68
% 11.91/4.57  Index Insertion      : 0.00
% 11.91/4.57  Index Deletion       : 0.00
% 11.91/4.57  Index Matching       : 0.00
% 11.91/4.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
