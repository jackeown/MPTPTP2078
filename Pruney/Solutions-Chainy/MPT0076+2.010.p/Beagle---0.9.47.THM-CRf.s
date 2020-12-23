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
% DateTime   : Thu Dec  3 09:43:33 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   31 (  37 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 (  58 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_68,negated_conjecture,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_53,axiom,(
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

tff(c_20,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    ! [B_17,A_18] :
      ( r1_xboole_0(B_17,A_18)
      | ~ r1_xboole_0(A_18,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_25,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_22])).

tff(c_53,plain,(
    ! [A_28,C_29,B_30] :
      ( r1_xboole_0(A_28,C_29)
      | ~ r1_xboole_0(B_30,C_29)
      | ~ r1_tarski(A_28,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_64,plain,(
    ! [A_28] :
      ( r1_xboole_0(A_28,'#skF_4')
      | ~ r1_tarski(A_28,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_25,c_53])).

tff(c_80,plain,(
    ! [A_33,B_34,C_35] :
      ( ~ r1_xboole_0(A_33,B_34)
      | ~ r2_hidden(C_35,B_34)
      | ~ r2_hidden(C_35,A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_188,plain,(
    ! [C_51,A_52] :
      ( ~ r2_hidden(C_51,'#skF_4')
      | ~ r2_hidden(C_51,A_52)
      | ~ r1_tarski(A_52,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_64,c_80])).

tff(c_197,plain,(
    ! [A_52] :
      ( ~ r2_hidden('#skF_1'('#skF_4'),A_52)
      | ~ r1_tarski(A_52,'#skF_3')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4,c_188])).

tff(c_203,plain,(
    ! [A_53] :
      ( ~ r2_hidden('#skF_1'('#skF_4'),A_53)
      | ~ r1_tarski(A_53,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_197])).

tff(c_207,plain,
    ( ~ r1_tarski('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_203])).

tff(c_210,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_207])).

tff(c_212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:25:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.27  
% 1.90/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.27  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.90/1.27  
% 1.90/1.27  %Foreground sorts:
% 1.90/1.27  
% 1.90/1.27  
% 1.90/1.27  %Background operators:
% 1.90/1.27  
% 1.90/1.27  
% 1.90/1.27  %Foreground operators:
% 1.90/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.90/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.90/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.27  tff('#skF_4', type, '#skF_4': $i).
% 1.90/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.90/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.90/1.27  
% 2.06/1.28  tff(f_68, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.06/1.28  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.06/1.28  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.06/1.28  tff(f_59, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.06/1.28  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.06/1.28  tff(c_20, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.06/1.28  tff(c_18, plain, (r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.06/1.28  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.28  tff(c_16, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.06/1.28  tff(c_22, plain, (![B_17, A_18]: (r1_xboole_0(B_17, A_18) | ~r1_xboole_0(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.28  tff(c_25, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_16, c_22])).
% 2.06/1.28  tff(c_53, plain, (![A_28, C_29, B_30]: (r1_xboole_0(A_28, C_29) | ~r1_xboole_0(B_30, C_29) | ~r1_tarski(A_28, B_30))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.06/1.28  tff(c_64, plain, (![A_28]: (r1_xboole_0(A_28, '#skF_4') | ~r1_tarski(A_28, '#skF_3'))), inference(resolution, [status(thm)], [c_25, c_53])).
% 2.06/1.28  tff(c_80, plain, (![A_33, B_34, C_35]: (~r1_xboole_0(A_33, B_34) | ~r2_hidden(C_35, B_34) | ~r2_hidden(C_35, A_33))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.06/1.28  tff(c_188, plain, (![C_51, A_52]: (~r2_hidden(C_51, '#skF_4') | ~r2_hidden(C_51, A_52) | ~r1_tarski(A_52, '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_80])).
% 2.06/1.28  tff(c_197, plain, (![A_52]: (~r2_hidden('#skF_1'('#skF_4'), A_52) | ~r1_tarski(A_52, '#skF_3') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_188])).
% 2.06/1.28  tff(c_203, plain, (![A_53]: (~r2_hidden('#skF_1'('#skF_4'), A_53) | ~r1_tarski(A_53, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_20, c_197])).
% 2.06/1.28  tff(c_207, plain, (~r1_tarski('#skF_4', '#skF_3') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_203])).
% 2.06/1.28  tff(c_210, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_207])).
% 2.06/1.28  tff(c_212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_210])).
% 2.06/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.28  
% 2.06/1.28  Inference rules
% 2.06/1.28  ----------------------
% 2.06/1.28  #Ref     : 0
% 2.06/1.28  #Sup     : 43
% 2.06/1.28  #Fact    : 0
% 2.06/1.28  #Define  : 0
% 2.06/1.28  #Split   : 3
% 2.06/1.28  #Chain   : 0
% 2.06/1.28  #Close   : 0
% 2.06/1.28  
% 2.06/1.28  Ordering : KBO
% 2.06/1.28  
% 2.06/1.28  Simplification rules
% 2.06/1.28  ----------------------
% 2.06/1.28  #Subsume      : 9
% 2.06/1.28  #Demod        : 5
% 2.06/1.28  #Tautology    : 5
% 2.06/1.28  #SimpNegUnit  : 4
% 2.06/1.28  #BackRed      : 0
% 2.06/1.28  
% 2.06/1.28  #Partial instantiations: 0
% 2.06/1.28  #Strategies tried      : 1
% 2.06/1.28  
% 2.06/1.28  Timing (in seconds)
% 2.06/1.28  ----------------------
% 2.06/1.28  Preprocessing        : 0.26
% 2.06/1.28  Parsing              : 0.15
% 2.06/1.28  CNF conversion       : 0.02
% 2.06/1.28  Main loop            : 0.19
% 2.06/1.28  Inferencing          : 0.08
% 2.06/1.28  Reduction            : 0.04
% 2.06/1.28  Demodulation         : 0.03
% 2.06/1.28  BG Simplification    : 0.01
% 2.06/1.28  Subsumption          : 0.05
% 2.06/1.28  Abstraction          : 0.01
% 2.06/1.28  MUC search           : 0.00
% 2.06/1.28  Cooper               : 0.00
% 2.06/1.28  Total                : 0.48
% 2.06/1.28  Index Insertion      : 0.00
% 2.06/1.28  Index Deletion       : 0.00
% 2.06/1.28  Index Matching       : 0.00
% 2.06/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
