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
% DateTime   : Thu Dec  3 09:45:34 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   28 (  37 expanded)
%              Number of leaves         :   12 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  66 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_xboole_0(A,D)
          & r1_xboole_0(B,D)
          & r1_xboole_0(C,D) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_16,plain,(
    r1_xboole_0('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_17,plain,(
    ! [B_6,A_7] :
      ( r1_xboole_0(B_6,A_7)
      | ~ r1_xboole_0(A_7,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    r1_xboole_0('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_17])).

tff(c_14,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_25,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_17])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( ~ r1_xboole_0(A_3,C_5)
      | ~ r1_xboole_0(A_3,B_4)
      | r1_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_17])).

tff(c_41,plain,(
    ! [A_14,C_15,B_16] :
      ( ~ r1_xboole_0(A_14,C_15)
      | ~ r1_xboole_0(A_14,B_16)
      | r1_xboole_0(A_14,k2_xboole_0(B_16,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [B_17,C_18,A_19] :
      ( r1_xboole_0(k2_xboole_0(B_17,C_18),A_19)
      | ~ r1_xboole_0(A_19,C_18)
      | ~ r1_xboole_0(A_19,B_17) ) ),
    inference(resolution,[status(thm)],[c_41,c_2])).

tff(c_10,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_64,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_3')
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_53,c_10])).

tff(c_71,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_64])).

tff(c_75,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_2')
    | ~ r1_xboole_0('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_71])).

tff(c_79,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_25,c_75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.12  
% 1.62/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.13  %$ r1_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.62/1.13  
% 1.62/1.13  %Foreground sorts:
% 1.62/1.13  
% 1.62/1.13  
% 1.62/1.13  %Background operators:
% 1.62/1.13  
% 1.62/1.13  
% 1.62/1.13  %Foreground operators:
% 1.62/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.62/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.62/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.62/1.13  
% 1.73/1.14  tff(f_54, negated_conjecture, ~(![A, B, C, D]: (((r1_xboole_0(A, D) & r1_xboole_0(B, D)) & r1_xboole_0(C, D)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_xboole_1)).
% 1.73/1.14  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.73/1.14  tff(f_45, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 1.73/1.14  tff(c_16, plain, (r1_xboole_0('#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.73/1.14  tff(c_17, plain, (![B_6, A_7]: (r1_xboole_0(B_6, A_7) | ~r1_xboole_0(A_7, B_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.73/1.14  tff(c_26, plain, (r1_xboole_0('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_16, c_17])).
% 1.73/1.14  tff(c_14, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.73/1.14  tff(c_25, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_14, c_17])).
% 1.73/1.14  tff(c_4, plain, (![A_3, C_5, B_4]: (~r1_xboole_0(A_3, C_5) | ~r1_xboole_0(A_3, B_4) | r1_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.73/1.14  tff(c_12, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.73/1.14  tff(c_24, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_17])).
% 1.73/1.14  tff(c_41, plain, (![A_14, C_15, B_16]: (~r1_xboole_0(A_14, C_15) | ~r1_xboole_0(A_14, B_16) | r1_xboole_0(A_14, k2_xboole_0(B_16, C_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.73/1.14  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.73/1.14  tff(c_53, plain, (![B_17, C_18, A_19]: (r1_xboole_0(k2_xboole_0(B_17, C_18), A_19) | ~r1_xboole_0(A_19, C_18) | ~r1_xboole_0(A_19, B_17))), inference(resolution, [status(thm)], [c_41, c_2])).
% 1.73/1.14  tff(c_10, plain, (~r1_xboole_0(k2_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.73/1.14  tff(c_64, plain, (~r1_xboole_0('#skF_4', '#skF_3') | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_53, c_10])).
% 1.73/1.14  tff(c_71, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_64])).
% 1.73/1.14  tff(c_75, plain, (~r1_xboole_0('#skF_4', '#skF_2') | ~r1_xboole_0('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_4, c_71])).
% 1.73/1.14  tff(c_79, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_25, c_75])).
% 1.73/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.14  
% 1.73/1.14  Inference rules
% 1.73/1.14  ----------------------
% 1.73/1.14  #Ref     : 0
% 1.73/1.14  #Sup     : 14
% 1.73/1.14  #Fact    : 0
% 1.73/1.14  #Define  : 0
% 1.73/1.14  #Split   : 0
% 1.73/1.14  #Chain   : 0
% 1.73/1.14  #Close   : 0
% 1.73/1.14  
% 1.73/1.14  Ordering : KBO
% 1.73/1.14  
% 1.73/1.14  Simplification rules
% 1.73/1.14  ----------------------
% 1.73/1.14  #Subsume      : 1
% 1.73/1.14  #Demod        : 6
% 1.73/1.14  #Tautology    : 5
% 1.73/1.14  #SimpNegUnit  : 0
% 1.73/1.14  #BackRed      : 0
% 1.73/1.14  
% 1.73/1.14  #Partial instantiations: 0
% 1.73/1.14  #Strategies tried      : 1
% 1.73/1.14  
% 1.73/1.14  Timing (in seconds)
% 1.73/1.14  ----------------------
% 1.73/1.14  Preprocessing        : 0.26
% 1.73/1.14  Parsing              : 0.14
% 1.73/1.14  CNF conversion       : 0.02
% 1.73/1.14  Main loop            : 0.12
% 1.73/1.14  Inferencing          : 0.05
% 1.73/1.14  Reduction            : 0.03
% 1.73/1.14  Demodulation         : 0.02
% 1.73/1.14  BG Simplification    : 0.01
% 1.73/1.14  Subsumption          : 0.03
% 1.73/1.14  Abstraction          : 0.00
% 1.73/1.14  MUC search           : 0.00
% 1.73/1.14  Cooper               : 0.00
% 1.73/1.14  Total                : 0.41
% 1.73/1.14  Index Insertion      : 0.00
% 1.73/1.14  Index Deletion       : 0.00
% 1.73/1.14  Index Matching       : 0.00
% 1.73/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
