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
% DateTime   : Thu Dec  3 09:42:27 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   29 (  51 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  83 expanded)
%              Number of equality atoms :    4 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,B)
                & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_12,plain,(
    ! [B_9] : ~ r2_xboole_0(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    ! [A_18,B_19] :
      ( r2_xboole_0(A_18,B_19)
      | B_19 = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    r2_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    ! [B_13,A_14] :
      ( ~ r2_xboole_0(B_13,A_14)
      | ~ r2_xboole_0(A_14,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_23,plain,(
    ~ r2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_20])).

tff(c_44,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_23])).

tff(c_48,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [C_11] :
      ( r2_hidden(C_11,'#skF_2')
      | ~ r2_hidden(C_11,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_49,plain,(
    ! [A_20,B_21] :
      ( ~ r2_hidden('#skF_1'(A_20,B_21),B_21)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_62,plain,(
    ! [A_25] :
      ( r1_tarski(A_25,'#skF_2')
      | ~ r2_hidden('#skF_1'(A_25,'#skF_2'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_49])).

tff(c_66,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_62])).

tff(c_70,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_66])).

tff(c_71,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_76,plain,(
    r2_xboole_0('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_18])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.13  
% 1.68/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.13  %$ r2_xboole_0 > r2_hidden > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.68/1.13  
% 1.68/1.13  %Foreground sorts:
% 1.68/1.13  
% 1.68/1.13  
% 1.68/1.13  %Background operators:
% 1.68/1.13  
% 1.68/1.13  
% 1.68/1.13  %Foreground operators:
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.13  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.68/1.13  
% 1.68/1.14  tff(f_44, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.68/1.14  tff(f_55, negated_conjecture, ~(![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 1.68/1.14  tff(f_30, axiom, (![A, B]: (r2_xboole_0(A, B) => ~r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 1.68/1.14  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.68/1.14  tff(c_12, plain, (![B_9]: (~r2_xboole_0(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.68/1.14  tff(c_30, plain, (![A_18, B_19]: (r2_xboole_0(A_18, B_19) | B_19=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.68/1.14  tff(c_18, plain, (r2_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.68/1.14  tff(c_20, plain, (![B_13, A_14]: (~r2_xboole_0(B_13, A_14) | ~r2_xboole_0(A_14, B_13))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.68/1.14  tff(c_23, plain, (~r2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_20])).
% 1.68/1.14  tff(c_44, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_23])).
% 1.68/1.14  tff(c_48, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_44])).
% 1.68/1.14  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.68/1.14  tff(c_16, plain, (![C_11]: (r2_hidden(C_11, '#skF_2') | ~r2_hidden(C_11, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.68/1.14  tff(c_49, plain, (![A_20, B_21]: (~r2_hidden('#skF_1'(A_20, B_21), B_21) | r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.68/1.14  tff(c_62, plain, (![A_25]: (r1_tarski(A_25, '#skF_2') | ~r2_hidden('#skF_1'(A_25, '#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_49])).
% 1.68/1.14  tff(c_66, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_8, c_62])).
% 1.68/1.14  tff(c_70, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_48, c_66])).
% 1.68/1.14  tff(c_71, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 1.68/1.14  tff(c_76, plain, (r2_xboole_0('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_18])).
% 1.68/1.14  tff(c_78, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_76])).
% 1.68/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.14  
% 1.68/1.14  Inference rules
% 1.68/1.14  ----------------------
% 1.68/1.14  #Ref     : 0
% 1.68/1.14  #Sup     : 9
% 1.68/1.14  #Fact    : 0
% 1.68/1.14  #Define  : 0
% 1.68/1.14  #Split   : 1
% 1.68/1.14  #Chain   : 0
% 1.68/1.14  #Close   : 0
% 1.68/1.14  
% 1.68/1.14  Ordering : KBO
% 1.68/1.14  
% 1.68/1.14  Simplification rules
% 1.68/1.14  ----------------------
% 1.68/1.14  #Subsume      : 1
% 1.68/1.14  #Demod        : 4
% 1.68/1.14  #Tautology    : 3
% 1.68/1.14  #SimpNegUnit  : 2
% 1.68/1.14  #BackRed      : 3
% 1.68/1.14  
% 1.68/1.14  #Partial instantiations: 0
% 1.68/1.14  #Strategies tried      : 1
% 1.68/1.14  
% 1.68/1.14  Timing (in seconds)
% 1.68/1.14  ----------------------
% 1.68/1.14  Preprocessing        : 0.25
% 1.68/1.14  Parsing              : 0.13
% 1.68/1.14  CNF conversion       : 0.02
% 1.68/1.14  Main loop            : 0.11
% 1.68/1.14  Inferencing          : 0.05
% 1.68/1.14  Reduction            : 0.03
% 1.68/1.14  Demodulation         : 0.01
% 1.68/1.14  BG Simplification    : 0.01
% 1.68/1.14  Subsumption          : 0.02
% 1.68/1.14  Abstraction          : 0.00
% 1.68/1.14  MUC search           : 0.00
% 1.68/1.14  Cooper               : 0.00
% 1.68/1.14  Total                : 0.38
% 1.68/1.14  Index Insertion      : 0.00
% 1.68/1.14  Index Deletion       : 0.00
% 1.68/1.14  Index Matching       : 0.00
% 1.68/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
