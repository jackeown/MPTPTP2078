%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:55 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   33 (  72 expanded)
%              Number of leaves         :   17 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :   55 ( 130 expanded)
%              Number of equality atoms :    4 (  20 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_hidden(A,B)
          & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C,D,E] :
      ~ ( r2_hidden(A,B)
        & r2_hidden(B,C)
        & r2_hidden(C,D)
        & r2_hidden(D,E)
        & r2_hidden(E,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_ordinal1)).

tff(c_30,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,(
    ! [A_20,B_21] :
      ( k2_xboole_0(A_20,B_21) = B_21
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_44,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_40])).

tff(c_49,plain,(
    ! [D_22,A_23,B_24] :
      ( ~ r2_hidden(D_22,A_23)
      | r2_hidden(D_22,k2_xboole_0(A_23,B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_52,plain,(
    ! [D_22] :
      ( ~ r2_hidden(D_22,'#skF_4')
      | r2_hidden(D_22,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_49])).

tff(c_79,plain,(
    ! [A_37,E_36,D_34,B_35,C_38] :
      ( ~ r2_hidden(E_36,A_37)
      | ~ r2_hidden(D_34,E_36)
      | ~ r2_hidden(C_38,D_34)
      | ~ r2_hidden(B_35,C_38)
      | ~ r2_hidden(A_37,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_274,plain,(
    ! [D_92,D_93,C_94,B_95] :
      ( ~ r2_hidden(D_92,D_93)
      | ~ r2_hidden(C_94,D_92)
      | ~ r2_hidden(B_95,C_94)
      | ~ r2_hidden('#skF_3',B_95)
      | ~ r2_hidden(D_93,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_79])).

tff(c_278,plain,(
    ! [C_94,D_22,B_95] :
      ( ~ r2_hidden(C_94,D_22)
      | ~ r2_hidden(B_95,C_94)
      | ~ r2_hidden('#skF_3',B_95)
      | ~ r2_hidden('#skF_3','#skF_4')
      | ~ r2_hidden(D_22,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_274])).

tff(c_289,plain,(
    ! [C_96,D_97,B_98] :
      ( ~ r2_hidden(C_96,D_97)
      | ~ r2_hidden(B_98,C_96)
      | ~ r2_hidden('#skF_3',B_98)
      | ~ r2_hidden(D_97,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_278])).

tff(c_293,plain,(
    ! [B_98,D_22] :
      ( ~ r2_hidden(B_98,D_22)
      | ~ r2_hidden('#skF_3',B_98)
      | ~ r2_hidden('#skF_3','#skF_4')
      | ~ r2_hidden(D_22,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_289])).

tff(c_317,plain,(
    ! [B_102,D_103] :
      ( ~ r2_hidden(B_102,D_103)
      | ~ r2_hidden('#skF_3',B_102)
      | ~ r2_hidden(D_103,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_293])).

tff(c_321,plain,(
    ! [D_22] :
      ( ~ r2_hidden('#skF_3',D_22)
      | ~ r2_hidden('#skF_3','#skF_4')
      | ~ r2_hidden(D_22,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_317])).

tff(c_332,plain,(
    ! [D_104] :
      ( ~ r2_hidden('#skF_3',D_104)
      | ~ r2_hidden(D_104,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_321])).

tff(c_338,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_332])).

tff(c_348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_338])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:55:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.28  
% 2.19/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.28  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.19/1.28  
% 2.19/1.28  %Foreground sorts:
% 2.19/1.28  
% 2.19/1.28  
% 2.19/1.28  %Background operators:
% 2.19/1.28  
% 2.19/1.28  
% 2.19/1.28  %Foreground operators:
% 2.19/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.19/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.28  
% 2.19/1.29  tff(f_59, negated_conjecture, ~(![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.19/1.29  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.19/1.29  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.19/1.29  tff(f_53, axiom, (![A, B, C, D, E]: ~((((r2_hidden(A, B) & r2_hidden(B, C)) & r2_hidden(C, D)) & r2_hidden(D, E)) & r2_hidden(E, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_ordinal1)).
% 2.19/1.29  tff(c_30, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.19/1.29  tff(c_28, plain, (r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.19/1.29  tff(c_40, plain, (![A_20, B_21]: (k2_xboole_0(A_20, B_21)=B_21 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.19/1.29  tff(c_44, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_28, c_40])).
% 2.19/1.29  tff(c_49, plain, (![D_22, A_23, B_24]: (~r2_hidden(D_22, A_23) | r2_hidden(D_22, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.19/1.29  tff(c_52, plain, (![D_22]: (~r2_hidden(D_22, '#skF_4') | r2_hidden(D_22, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_49])).
% 2.19/1.29  tff(c_79, plain, (![A_37, E_36, D_34, B_35, C_38]: (~r2_hidden(E_36, A_37) | ~r2_hidden(D_34, E_36) | ~r2_hidden(C_38, D_34) | ~r2_hidden(B_35, C_38) | ~r2_hidden(A_37, B_35))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.19/1.29  tff(c_274, plain, (![D_92, D_93, C_94, B_95]: (~r2_hidden(D_92, D_93) | ~r2_hidden(C_94, D_92) | ~r2_hidden(B_95, C_94) | ~r2_hidden('#skF_3', B_95) | ~r2_hidden(D_93, '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_79])).
% 2.19/1.29  tff(c_278, plain, (![C_94, D_22, B_95]: (~r2_hidden(C_94, D_22) | ~r2_hidden(B_95, C_94) | ~r2_hidden('#skF_3', B_95) | ~r2_hidden('#skF_3', '#skF_4') | ~r2_hidden(D_22, '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_274])).
% 2.19/1.29  tff(c_289, plain, (![C_96, D_97, B_98]: (~r2_hidden(C_96, D_97) | ~r2_hidden(B_98, C_96) | ~r2_hidden('#skF_3', B_98) | ~r2_hidden(D_97, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_278])).
% 2.19/1.29  tff(c_293, plain, (![B_98, D_22]: (~r2_hidden(B_98, D_22) | ~r2_hidden('#skF_3', B_98) | ~r2_hidden('#skF_3', '#skF_4') | ~r2_hidden(D_22, '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_289])).
% 2.19/1.29  tff(c_317, plain, (![B_102, D_103]: (~r2_hidden(B_102, D_103) | ~r2_hidden('#skF_3', B_102) | ~r2_hidden(D_103, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_293])).
% 2.19/1.29  tff(c_321, plain, (![D_22]: (~r2_hidden('#skF_3', D_22) | ~r2_hidden('#skF_3', '#skF_4') | ~r2_hidden(D_22, '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_317])).
% 2.19/1.29  tff(c_332, plain, (![D_104]: (~r2_hidden('#skF_3', D_104) | ~r2_hidden(D_104, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_321])).
% 2.19/1.29  tff(c_338, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_332])).
% 2.19/1.29  tff(c_348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_338])).
% 2.19/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.29  
% 2.19/1.29  Inference rules
% 2.19/1.29  ----------------------
% 2.19/1.29  #Ref     : 0
% 2.19/1.29  #Sup     : 78
% 2.19/1.29  #Fact    : 0
% 2.19/1.29  #Define  : 0
% 2.19/1.29  #Split   : 0
% 2.19/1.29  #Chain   : 0
% 2.19/1.29  #Close   : 0
% 2.19/1.29  
% 2.19/1.29  Ordering : KBO
% 2.19/1.29  
% 2.19/1.29  Simplification rules
% 2.19/1.29  ----------------------
% 2.19/1.29  #Subsume      : 19
% 2.19/1.29  #Demod        : 13
% 2.19/1.29  #Tautology    : 10
% 2.19/1.29  #SimpNegUnit  : 0
% 2.19/1.29  #BackRed      : 0
% 2.19/1.29  
% 2.19/1.29  #Partial instantiations: 0
% 2.19/1.29  #Strategies tried      : 1
% 2.19/1.29  
% 2.19/1.29  Timing (in seconds)
% 2.19/1.29  ----------------------
% 2.19/1.29  Preprocessing        : 0.29
% 2.19/1.29  Parsing              : 0.15
% 2.19/1.29  CNF conversion       : 0.02
% 2.19/1.29  Main loop            : 0.23
% 2.19/1.29  Inferencing          : 0.08
% 2.19/1.29  Reduction            : 0.05
% 2.19/1.29  Demodulation         : 0.04
% 2.19/1.29  BG Simplification    : 0.01
% 2.19/1.29  Subsumption          : 0.07
% 2.19/1.29  Abstraction          : 0.01
% 2.19/1.29  MUC search           : 0.00
% 2.19/1.29  Cooper               : 0.00
% 2.19/1.29  Total                : 0.54
% 2.19/1.29  Index Insertion      : 0.00
% 2.19/1.29  Index Deletion       : 0.00
% 2.19/1.29  Index Matching       : 0.00
% 2.19/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
