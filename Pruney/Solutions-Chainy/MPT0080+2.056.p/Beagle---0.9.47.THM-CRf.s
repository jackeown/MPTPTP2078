%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:56 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   36 (  40 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  61 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | k4_xboole_0(A_16,B_17) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_16])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_104,plain,(
    ! [A_22,B_23,C_24] :
      ( r1_tarski(k4_xboole_0(A_22,B_23),C_24)
      | ~ r1_tarski(A_22,k2_xboole_0(B_23,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_330,plain,(
    ! [A_47,B_48,C_49] :
      ( k4_xboole_0(k4_xboole_0(A_47,B_48),C_49) = k1_xboole_0
      | ~ r1_tarski(A_47,k2_xboole_0(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_104,c_6])).

tff(c_354,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_330])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_196,plain,(
    ! [A_34,C_35,B_36,D_37] :
      ( r1_xboole_0(A_34,C_35)
      | ~ r1_xboole_0(B_36,D_37)
      | ~ r1_tarski(C_35,D_37)
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_261,plain,(
    ! [A_42,C_43] :
      ( r1_xboole_0(A_42,C_43)
      | ~ r1_tarski(C_43,'#skF_3')
      | ~ r1_tarski(A_42,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_196])).

tff(c_14,plain,(
    ! [A_12] :
      ( ~ r1_xboole_0(A_12,A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_304,plain,(
    ! [C_46] :
      ( k1_xboole_0 = C_46
      | ~ r1_tarski(C_46,'#skF_3')
      | ~ r1_tarski(C_46,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_261,c_14])).

tff(c_488,plain,(
    ! [A_60] :
      ( k1_xboole_0 = A_60
      | ~ r1_tarski(A_60,'#skF_1')
      | k4_xboole_0(A_60,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_304])).

tff(c_662,plain,(
    ! [B_66] :
      ( k4_xboole_0('#skF_1',B_66) = k1_xboole_0
      | k4_xboole_0(k4_xboole_0('#skF_1',B_66),'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_488])).

tff(c_665,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_662])).

tff(c_672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_665])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:19:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.34  
% 2.44/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.35  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.44/1.35  
% 2.44/1.35  %Foreground sorts:
% 2.44/1.35  
% 2.44/1.35  
% 2.44/1.35  %Background operators:
% 2.44/1.35  
% 2.44/1.35  
% 2.44/1.35  %Foreground operators:
% 2.44/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.44/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.44/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.44/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.44/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.44/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.44/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.44/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.44/1.35  
% 2.44/1.36  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 2.44/1.36  tff(f_62, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 2.44/1.36  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.44/1.36  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.44/1.36  tff(f_43, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_xboole_1)).
% 2.44/1.36  tff(f_55, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.44/1.36  tff(c_28, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | k4_xboole_0(A_16, B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.36  tff(c_16, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.44/1.36  tff(c_32, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_16])).
% 2.44/1.36  tff(c_20, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.44/1.36  tff(c_104, plain, (![A_22, B_23, C_24]: (r1_tarski(k4_xboole_0(A_22, B_23), C_24) | ~r1_tarski(A_22, k2_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.44/1.36  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.36  tff(c_330, plain, (![A_47, B_48, C_49]: (k4_xboole_0(k4_xboole_0(A_47, B_48), C_49)=k1_xboole_0 | ~r1_tarski(A_47, k2_xboole_0(B_48, C_49)))), inference(resolution, [status(thm)], [c_104, c_6])).
% 2.44/1.36  tff(c_354, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_330])).
% 2.44/1.36  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.44/1.36  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.36  tff(c_18, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.44/1.36  tff(c_196, plain, (![A_34, C_35, B_36, D_37]: (r1_xboole_0(A_34, C_35) | ~r1_xboole_0(B_36, D_37) | ~r1_tarski(C_35, D_37) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.44/1.36  tff(c_261, plain, (![A_42, C_43]: (r1_xboole_0(A_42, C_43) | ~r1_tarski(C_43, '#skF_3') | ~r1_tarski(A_42, '#skF_1'))), inference(resolution, [status(thm)], [c_18, c_196])).
% 2.44/1.36  tff(c_14, plain, (![A_12]: (~r1_xboole_0(A_12, A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.44/1.36  tff(c_304, plain, (![C_46]: (k1_xboole_0=C_46 | ~r1_tarski(C_46, '#skF_3') | ~r1_tarski(C_46, '#skF_1'))), inference(resolution, [status(thm)], [c_261, c_14])).
% 2.44/1.36  tff(c_488, plain, (![A_60]: (k1_xboole_0=A_60 | ~r1_tarski(A_60, '#skF_1') | k4_xboole_0(A_60, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_304])).
% 2.44/1.36  tff(c_662, plain, (![B_66]: (k4_xboole_0('#skF_1', B_66)=k1_xboole_0 | k4_xboole_0(k4_xboole_0('#skF_1', B_66), '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_488])).
% 2.44/1.36  tff(c_665, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_354, c_662])).
% 2.44/1.36  tff(c_672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_665])).
% 2.44/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.36  
% 2.44/1.36  Inference rules
% 2.44/1.36  ----------------------
% 2.44/1.36  #Ref     : 0
% 2.44/1.36  #Sup     : 147
% 2.44/1.36  #Fact    : 0
% 2.44/1.36  #Define  : 0
% 2.44/1.36  #Split   : 1
% 2.44/1.36  #Chain   : 0
% 2.44/1.36  #Close   : 0
% 2.44/1.36  
% 2.44/1.36  Ordering : KBO
% 2.44/1.36  
% 2.44/1.36  Simplification rules
% 2.44/1.36  ----------------------
% 2.44/1.36  #Subsume      : 2
% 2.44/1.36  #Demod        : 94
% 2.44/1.36  #Tautology    : 104
% 2.44/1.36  #SimpNegUnit  : 1
% 2.44/1.36  #BackRed      : 3
% 2.44/1.36  
% 2.44/1.36  #Partial instantiations: 0
% 2.44/1.36  #Strategies tried      : 1
% 2.44/1.36  
% 2.44/1.36  Timing (in seconds)
% 2.44/1.36  ----------------------
% 2.44/1.36  Preprocessing        : 0.27
% 2.44/1.36  Parsing              : 0.16
% 2.44/1.36  CNF conversion       : 0.01
% 2.44/1.36  Main loop            : 0.29
% 2.44/1.36  Inferencing          : 0.11
% 2.44/1.36  Reduction            : 0.08
% 2.44/1.36  Demodulation         : 0.06
% 2.44/1.36  BG Simplification    : 0.01
% 2.44/1.36  Subsumption          : 0.06
% 2.44/1.36  Abstraction          : 0.01
% 2.44/1.36  MUC search           : 0.00
% 2.44/1.36  Cooper               : 0.00
% 2.44/1.36  Total                : 0.58
% 2.44/1.36  Index Insertion      : 0.00
% 2.44/1.36  Index Deletion       : 0.00
% 2.44/1.36  Index Matching       : 0.00
% 2.44/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
