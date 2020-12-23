%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:31 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   35 (  46 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  69 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ~ ( r1_tarski(C,A)
            & r1_tarski(C,B)
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_20,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_67,plain,(
    ! [A_25,C_26,B_27] :
      ( r1_xboole_0(A_25,C_26)
      | ~ r1_xboole_0(B_27,C_26)
      | ~ r1_tarski(A_25,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_71,plain,(
    ! [A_28] :
      ( r1_xboole_0(A_28,'#skF_4')
      | ~ r1_tarski(A_28,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_67])).

tff(c_16,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_27,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_16,c_27])).

tff(c_44,plain,(
    ! [A_20,B_21,C_22] :
      ( ~ r1_xboole_0(A_20,B_21)
      | ~ r2_hidden(C_22,k3_xboole_0(A_20,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_50,plain,(
    ! [C_22] :
      ( ~ r1_xboole_0('#skF_5','#skF_4')
      | ~ r2_hidden(C_22,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_44])).

tff(c_57,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_76,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_57])).

tff(c_81,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_76])).

tff(c_84,plain,(
    ! [C_29] : ~ r2_hidden(C_29,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_88,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_84])).

tff(c_92,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:55:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.10  
% 1.70/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.10  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 1.70/1.10  
% 1.70/1.10  %Foreground sorts:
% 1.70/1.10  
% 1.70/1.10  
% 1.70/1.10  %Background operators:
% 1.70/1.10  
% 1.70/1.10  
% 1.70/1.10  %Foreground operators:
% 1.70/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.10  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.70/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.10  tff('#skF_5', type, '#skF_5': $i).
% 1.70/1.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.70/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.10  tff('#skF_4', type, '#skF_4': $i).
% 1.70/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.10  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.70/1.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.70/1.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.70/1.10  
% 1.70/1.11  tff(f_66, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 1.70/1.11  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.70/1.11  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.70/1.11  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.70/1.11  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.70/1.11  tff(c_20, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.70/1.11  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.70/1.11  tff(c_18, plain, (r1_tarski('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.70/1.11  tff(c_14, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.70/1.11  tff(c_67, plain, (![A_25, C_26, B_27]: (r1_xboole_0(A_25, C_26) | ~r1_xboole_0(B_27, C_26) | ~r1_tarski(A_25, B_27))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.70/1.11  tff(c_71, plain, (![A_28]: (r1_xboole_0(A_28, '#skF_4') | ~r1_tarski(A_28, '#skF_3'))), inference(resolution, [status(thm)], [c_14, c_67])).
% 1.70/1.11  tff(c_16, plain, (r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.70/1.11  tff(c_27, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.70/1.11  tff(c_34, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_16, c_27])).
% 1.70/1.11  tff(c_44, plain, (![A_20, B_21, C_22]: (~r1_xboole_0(A_20, B_21) | ~r2_hidden(C_22, k3_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.70/1.11  tff(c_50, plain, (![C_22]: (~r1_xboole_0('#skF_5', '#skF_4') | ~r2_hidden(C_22, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_44])).
% 1.70/1.11  tff(c_57, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 1.70/1.11  tff(c_76, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_71, c_57])).
% 1.70/1.11  tff(c_81, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_76])).
% 1.70/1.11  tff(c_84, plain, (![C_29]: (~r2_hidden(C_29, '#skF_5'))), inference(splitRight, [status(thm)], [c_50])).
% 1.70/1.11  tff(c_88, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_84])).
% 1.70/1.11  tff(c_92, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_88])).
% 1.70/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.11  
% 1.70/1.11  Inference rules
% 1.70/1.11  ----------------------
% 1.70/1.11  #Ref     : 0
% 1.70/1.11  #Sup     : 16
% 1.70/1.11  #Fact    : 0
% 1.70/1.11  #Define  : 0
% 1.70/1.11  #Split   : 2
% 1.70/1.11  #Chain   : 0
% 1.70/1.11  #Close   : 0
% 1.70/1.11  
% 1.70/1.11  Ordering : KBO
% 1.70/1.11  
% 1.70/1.11  Simplification rules
% 1.70/1.11  ----------------------
% 1.70/1.11  #Subsume      : 2
% 1.70/1.11  #Demod        : 1
% 1.70/1.11  #Tautology    : 5
% 1.70/1.11  #SimpNegUnit  : 3
% 1.70/1.11  #BackRed      : 0
% 1.70/1.11  
% 1.70/1.11  #Partial instantiations: 0
% 1.70/1.11  #Strategies tried      : 1
% 1.70/1.11  
% 1.70/1.11  Timing (in seconds)
% 1.70/1.11  ----------------------
% 1.70/1.11  Preprocessing        : 0.25
% 1.70/1.11  Parsing              : 0.14
% 1.70/1.11  CNF conversion       : 0.02
% 1.70/1.11  Main loop            : 0.11
% 1.70/1.11  Inferencing          : 0.05
% 1.70/1.11  Reduction            : 0.03
% 1.70/1.11  Demodulation         : 0.02
% 1.70/1.11  BG Simplification    : 0.01
% 1.70/1.11  Subsumption          : 0.01
% 1.70/1.11  Abstraction          : 0.00
% 1.70/1.11  MUC search           : 0.00
% 1.70/1.11  Cooper               : 0.00
% 1.70/1.11  Total                : 0.38
% 1.70/1.11  Index Insertion      : 0.00
% 1.70/1.11  Index Deletion       : 0.00
% 1.70/1.11  Index Matching       : 0.00
% 1.70/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
