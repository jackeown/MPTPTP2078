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
% DateTime   : Thu Dec  3 09:44:31 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  30 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_xboole_0(k4_xboole_0(A_8,B_9),B_9) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_27,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_31,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_16,c_27])).

tff(c_58,plain,(
    ! [A_24,B_25,C_26] :
      ( r1_xboole_0(A_24,B_25)
      | ~ r1_xboole_0(A_24,k2_xboole_0(B_25,C_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_72,plain,(
    ! [A_27] :
      ( r1_xboole_0(A_27,'#skF_1')
      | ~ r1_xboole_0(A_27,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_58])).

tff(c_83,plain,(
    ! [A_28] : r1_xboole_0(k4_xboole_0(A_28,'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_72])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_86,plain,(
    ! [A_28] : r1_xboole_0('#skF_1',k4_xboole_0(A_28,'#skF_2')) ),
    inference(resolution,[status(thm)],[c_83,c_2])).

tff(c_14,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_89,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:57:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.15  
% 1.76/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.15  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.76/1.15  
% 1.76/1.15  %Foreground sorts:
% 1.76/1.15  
% 1.76/1.15  
% 1.76/1.15  %Background operators:
% 1.76/1.15  
% 1.76/1.15  
% 1.76/1.15  %Foreground operators:
% 1.76/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.76/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.76/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.76/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.76/1.15  
% 1.76/1.16  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.76/1.16  tff(f_56, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.76/1.16  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.76/1.16  tff(f_49, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 1.76/1.16  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.76/1.16  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(k4_xboole_0(A_8, B_9), B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.76/1.16  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.76/1.16  tff(c_27, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.76/1.16  tff(c_31, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_16, c_27])).
% 1.76/1.16  tff(c_58, plain, (![A_24, B_25, C_26]: (r1_xboole_0(A_24, B_25) | ~r1_xboole_0(A_24, k2_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.76/1.16  tff(c_72, plain, (![A_27]: (r1_xboole_0(A_27, '#skF_1') | ~r1_xboole_0(A_27, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_31, c_58])).
% 1.76/1.16  tff(c_83, plain, (![A_28]: (r1_xboole_0(k4_xboole_0(A_28, '#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_12, c_72])).
% 1.76/1.16  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.76/1.16  tff(c_86, plain, (![A_28]: (r1_xboole_0('#skF_1', k4_xboole_0(A_28, '#skF_2')))), inference(resolution, [status(thm)], [c_83, c_2])).
% 1.76/1.16  tff(c_14, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.76/1.16  tff(c_89, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_14])).
% 1.76/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.16  
% 1.76/1.16  Inference rules
% 1.76/1.16  ----------------------
% 1.76/1.16  #Ref     : 0
% 1.76/1.16  #Sup     : 16
% 1.76/1.16  #Fact    : 0
% 1.76/1.16  #Define  : 0
% 1.76/1.16  #Split   : 0
% 1.76/1.16  #Chain   : 0
% 1.76/1.16  #Close   : 0
% 1.76/1.16  
% 1.76/1.16  Ordering : KBO
% 1.76/1.16  
% 1.76/1.16  Simplification rules
% 1.76/1.16  ----------------------
% 1.76/1.16  #Subsume      : 0
% 1.76/1.16  #Demod        : 3
% 1.76/1.16  #Tautology    : 5
% 1.76/1.16  #SimpNegUnit  : 0
% 1.76/1.16  #BackRed      : 1
% 1.76/1.16  
% 1.76/1.16  #Partial instantiations: 0
% 1.76/1.16  #Strategies tried      : 1
% 1.76/1.16  
% 1.76/1.16  Timing (in seconds)
% 1.76/1.16  ----------------------
% 1.76/1.16  Preprocessing        : 0.27
% 1.76/1.16  Parsing              : 0.15
% 1.76/1.16  CNF conversion       : 0.02
% 1.76/1.16  Main loop            : 0.12
% 1.76/1.16  Inferencing          : 0.05
% 1.76/1.16  Reduction            : 0.03
% 1.76/1.16  Demodulation         : 0.03
% 1.76/1.16  BG Simplification    : 0.01
% 1.76/1.16  Subsumption          : 0.02
% 1.76/1.16  Abstraction          : 0.00
% 1.76/1.16  MUC search           : 0.00
% 1.76/1.16  Cooper               : 0.00
% 1.76/1.16  Total                : 0.41
% 1.76/1.16  Index Insertion      : 0.00
% 1.76/1.16  Index Deletion       : 0.00
% 1.76/1.16  Index Matching       : 0.00
% 1.76/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
