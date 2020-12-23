%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:33 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  44 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_4 > #skF_2

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
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ~ ( r1_tarski(B,A)
            & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_20,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_36,plain,(
    ! [B_21,A_22] :
      ( r1_xboole_0(B_21,A_22)
      | ~ r1_xboole_0(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_39,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_36])).

tff(c_53,plain,(
    ! [A_26,C_27,B_28] :
      ( r1_xboole_0(A_26,C_27)
      | ~ r1_xboole_0(B_28,C_27)
      | ~ r1_tarski(A_26,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_72,plain,(
    ! [A_32] :
      ( r1_xboole_0(A_32,'#skF_4')
      | ~ r1_tarski(A_32,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_39,c_53])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    ! [A_23,B_24,C_25] :
      ( ~ r1_xboole_0(A_23,B_24)
      | ~ r2_hidden(C_25,k3_xboole_0(A_23,B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_51,plain,(
    ! [A_5,C_25] :
      ( ~ r1_xboole_0(A_5,A_5)
      | ~ r2_hidden(C_25,A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_44])).

tff(c_75,plain,(
    ! [C_25] :
      ( ~ r2_hidden(C_25,'#skF_4')
      | ~ r1_tarski('#skF_4','#skF_3') ) ),
    inference(resolution,[status(thm)],[c_72,c_51])).

tff(c_85,plain,(
    ! [C_33] : ~ r2_hidden(C_33,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_75])).

tff(c_89,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_85])).

tff(c_93,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:13:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.14  
% 1.74/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.15  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.74/1.15  
% 1.74/1.15  %Foreground sorts:
% 1.74/1.15  
% 1.74/1.15  
% 1.74/1.15  %Background operators:
% 1.74/1.15  
% 1.74/1.15  
% 1.74/1.15  %Foreground operators:
% 1.74/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.74/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.74/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.74/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.74/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.74/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.74/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.74/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.74/1.15  
% 1.74/1.16  tff(f_66, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.74/1.16  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.74/1.16  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.74/1.16  tff(f_57, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.74/1.16  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.74/1.16  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.74/1.16  tff(c_20, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.74/1.16  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.74/1.16  tff(c_18, plain, (r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.74/1.16  tff(c_16, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.74/1.16  tff(c_36, plain, (![B_21, A_22]: (r1_xboole_0(B_21, A_22) | ~r1_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.74/1.16  tff(c_39, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_16, c_36])).
% 1.74/1.16  tff(c_53, plain, (![A_26, C_27, B_28]: (r1_xboole_0(A_26, C_27) | ~r1_xboole_0(B_28, C_27) | ~r1_tarski(A_26, B_28))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.74/1.16  tff(c_72, plain, (![A_32]: (r1_xboole_0(A_32, '#skF_4') | ~r1_tarski(A_32, '#skF_3'))), inference(resolution, [status(thm)], [c_39, c_53])).
% 1.74/1.16  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.74/1.16  tff(c_44, plain, (![A_23, B_24, C_25]: (~r1_xboole_0(A_23, B_24) | ~r2_hidden(C_25, k3_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.74/1.16  tff(c_51, plain, (![A_5, C_25]: (~r1_xboole_0(A_5, A_5) | ~r2_hidden(C_25, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_44])).
% 1.74/1.16  tff(c_75, plain, (![C_25]: (~r2_hidden(C_25, '#skF_4') | ~r1_tarski('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_51])).
% 1.74/1.16  tff(c_85, plain, (![C_33]: (~r2_hidden(C_33, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_75])).
% 1.74/1.16  tff(c_89, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_85])).
% 1.74/1.16  tff(c_93, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_89])).
% 1.74/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.16  
% 1.74/1.16  Inference rules
% 1.74/1.16  ----------------------
% 1.74/1.16  #Ref     : 0
% 1.74/1.16  #Sup     : 16
% 1.74/1.16  #Fact    : 0
% 1.74/1.16  #Define  : 0
% 1.74/1.16  #Split   : 0
% 1.74/1.16  #Chain   : 0
% 1.74/1.16  #Close   : 0
% 1.74/1.16  
% 1.74/1.16  Ordering : KBO
% 1.74/1.16  
% 1.74/1.16  Simplification rules
% 1.74/1.16  ----------------------
% 1.74/1.16  #Subsume      : 0
% 1.74/1.16  #Demod        : 2
% 1.74/1.16  #Tautology    : 4
% 1.74/1.16  #SimpNegUnit  : 1
% 1.74/1.16  #BackRed      : 0
% 1.74/1.16  
% 1.74/1.16  #Partial instantiations: 0
% 1.74/1.16  #Strategies tried      : 1
% 1.74/1.16  
% 1.74/1.16  Timing (in seconds)
% 1.74/1.16  ----------------------
% 1.74/1.16  Preprocessing        : 0.26
% 1.74/1.16  Parsing              : 0.15
% 1.74/1.16  CNF conversion       : 0.02
% 1.74/1.16  Main loop            : 0.11
% 1.74/1.16  Inferencing          : 0.05
% 1.74/1.16  Reduction            : 0.03
% 1.74/1.16  Demodulation         : 0.02
% 1.74/1.16  BG Simplification    : 0.01
% 1.74/1.16  Subsumption          : 0.02
% 1.74/1.16  Abstraction          : 0.00
% 1.74/1.16  MUC search           : 0.00
% 1.74/1.16  Cooper               : 0.00
% 1.74/1.16  Total                : 0.39
% 1.74/1.16  Index Insertion      : 0.00
% 1.74/1.16  Index Deletion       : 0.00
% 1.74/1.16  Index Matching       : 0.00
% 1.74/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
